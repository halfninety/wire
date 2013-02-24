/** @license MIT License (c) copyright B Cavalier & J Hann */

/**
 * Licensed under the MIT License at:
 * http://www.opensource.org/licenses/mit-license.php
 */

(function(define){
define(['require', 'when', 'when/timeout', './array', './object', './moduleLoader', './lifecycle', './resolver', '../base'],
function(require, when, timeout, array, object, createModuleLoader, Lifecycle, Resolver, basePlugin) {

	"use strict";

	var defer, chain, whenAll,
		emptyObject,
		undef;

	// Local refs to when.js
	defer = when.defer;
	chain = when.chain;
	whenAll = when.all;

	emptyObject = {};

	function WireContext() {}

	/**
	 * Creates a new context from the supplied specs, with the supplied parent context.
	 * If specs is an {Array}, it may be a mixed array of string module ids, and object
	 * literal specs.  All spec module ids will be loaded, and then all specs will be
	 * merged from left-to-right (rightmost wins), and the resulting, merged spec will
	 * be wired.
	 *
	 * @private
	 *
	 * @param specs {String|Array|*}
	 * @param parent {Object} parent content
	 *
	 * @return {Promise} a promise for the new context
	 */
	function createContext(specs, parent, options) {
		// Do the actual wiring after all specs have been loaded
		function doWireContext(spec) {
			return createScope(spec, parent, options);
		}

		var moduleLoader = getModuleLoader(parent, options);

		return when(specs, function(specs) {
			return Array.isArray(specs)
				? when(ensureAllSpecsLoaded(specs, moduleLoader), doWireContext)
				: when(isString(specs) ? moduleLoader(specs) : specs, doWireContext);
		});
	}

	return createContext;

	/**
	 * Do the work of creating a new scope and fully wiring its contents
	 * @private
	 *
	 * @param scopeDef {Object} The spec (or portion of a spec) to be wired into a new scope
	 * @param parent {scope} scope to use as the parent, and thus from which to inherit
	 *  plugins, components, etc.
	 * @param [options] {Object} scope options
	 *
	 * @return {Promise} a promise for the new scope
	 */
	function createScope(scopeDef, parent, options) {
		var scope, scopeParent, context, config, contextHandlers,
			proxiedComponents, components, lifecycle, resolver, inflightRefs,
			pluginApi, resolvers, factories, facets, listeners, proxiers,
			moduleLoader, modulesToLoad, plugins,
			wireApi, modulesReady, scopeReady, scopeDestroyed, doDestroy;

		// `_getPluginApi` is a function that returns a pluginApi instance bond with
		// the given `_origin` value (so that we can reuse old instances). `pluginApi`
		// points to a special pluginApi instance bond with `_origin` value undefined,
		// to ensure compatibility. In fact, all other pluginApi instances use `pluginApi`
		// as prototype to inherit its properties, so adding a property to `pluginApi`
		// will make it visible in all pluginApi instances.
		var _getPluginApi;

		var _childScopes;

		inflightRefs = [];

		// Empty parent scope if none provided
		if(!parent) { parent = {}; }
		if(!options) { options = {}; }

		inheritFromParent(parent, options);
		createPluginApi();

		// TODO: Find a better way to load and scan the base plugin
		scanPlugin(basePlugin);

		configureContext(options);
		pluginApi.resolver = resolver;

		// Setup overwritable doDestroy so that this context
		// can only be destroyed once
		doDestroy = function () {
			// Retain a do-nothing doDestroy() func, in case
			// it is called again for some reason.
			doDestroy = function () {
			};

			return when(destroyContext(), executeDestroyers);
		};

		context = {
			spec: scopeDef,
			components: components,
			config: config
		};

		function executeInitializers() {
			return sequence(contextHandlers.init, context);
		}
		function executeDestroyers() {
			return sequence(contextHandlers.destroy, context);
		}

		return executeInitializers()
			.then(function() {

				var componentsToCreate = parseSpec(scopeDef, scopeReady);

				createComponents(componentsToCreate, scopeDef);

				// Once all modules are loaded, all the components can finish
				ensureAllModulesLoaded();

				// Return promise
				// Context will be ready when this promise resolves
				return scopeReady.promise;
			});

		//
		// Initialization
		//

		function inheritFromParent(parent, options) {
			// Descend scope and plugins from parent so that this scope can
			// use them directly via the prototype chain

			WireContext.prototype = createWireApi(object.inherit(parent.components));
			components = new WireContext();
			WireContext.prototype = undef;

			resolvers = object.inherit(parent.resolvers);
			factories = object.inherit(parent.factories);
			facets = object.inherit(parent.facets);

			// Set/override integral resolvers and factories
			resolvers.wire = wireResolver;
			factories.wire = wireFactory;

			listeners = array.delegate(parent.listeners);

			// Proxies is an array, have to concat
			proxiers = array.delegate(parent.proxiers);
			proxiedComponents = [];
			_childScopes = [];

			plugins = [];
			modulesToLoad = [];
			modulesReady = defer();

			scopeReady = defer();
			scopeDestroyed = defer();

			moduleLoader = getModuleLoader(parent, options);

			// A proxy of this scope that can be used as a parent to
			// any child scopes that may be created.
			scopeParent = {
				moduleLoader: moduleLoader,
				components: components,
				destroyed: scopeDestroyed,
				_childScopes: _childScopes
			};

			// Full scope definition.  This will be given to sub-scopes,
			// but should never be given to child contexts
			scope = Object.create(scopeParent);

			scope.resolvers = resolvers;
			scope.factories = factories;
			scope.facets = facets;
			scope.listeners = listeners;
			scope.proxiers = proxiers;
			scope.resolveRef = resolveRefName;
			scope.destroy = destroy;
			scope.path = createPath(options.name, parent.path);
			scope._origin = options._origin;

			// Expose `scope` and `proxiedComponents` through `WireApi`
			scope._proxiedComponents = proxiedComponents;
			scope._childScopes = _childScopes;
			scope._destroyChildren = _destroyChildren;
			components.__proto__._scope = scope;

			// When the parent begins its destroy phase, this child must
			// begin its destroy phase and complete it before the parent.
			// The context hierarchy will be destroyed from child to parent.
			// if (parent.destroyed) {
			//  	when(parent.destroyed, destroy);
			// }
			//
			// Now we simply keep a list of all (direct) child scopes in
			// the parent scope and destroy them when the parent is destroyed.
			if (parent._childScopes) {
				parent._childScopes.push(scope);
			}
		}

		function createWireApi(context) {
			wireApi = context.wire = wireChild;
			wireApi.destroy = context.destroy = apiDestroy;

			// Consider deprecating resolve
			// Any reference you could resolve using this should simply be
			// injected instead.
			wireApi.resolve = context.resolve = apiResolveRef;

			// Expose the ability to wire components into the scope
			// As in vanilla pluginApi, we assume an _origin value of undefined here,
			// which essentially means that all components created by calling this
			// function are considered top-level.
			context._wireComponent = function (spec, name, path) {
				// This is used both as name and _origin
				var n = createPath(name, path);
				return createItem(spec, n, n);
			};

			return context;
		}

		function createPluginApi() {
			// Plugin API
			// wire() API that is passed to plugins.
			var _pluginApiCache = {};

			pluginApi = function (spec, name, path) {
				var n = createPath(name, path);
				return createItem(spec, n, n);
			};

			pluginApi.resolveRef = apiResolveRef;
			pluginApi.getProxy = getProxy;
			pluginApi.loadModule = getModule;

			// Expose `scope` through `PluginApi`
			pluginApi._scope = scope;

			// Implement the cache and _getPluginApi() function
			_pluginApiCache[undef] = pluginApi;

			_getPluginApi = function(_origin) {
				if (_pluginApiCache[_origin]) {
					return _pluginApiCache[_origin];
				} else {
					// Create a pluginApi instance using `pluginApi` as prototype
					var instance = function(spec, name, path) {
						// We can't modify _origin in this function, because this
						// instance needs to be reusable.
						var n = createPath(name, path);
						return createItem(spec, n, n ? n : _origin);
					};
					instance._origin = _origin;
					instance.__proto__ = pluginApi;
					_pluginApiCache[_origin] = instance;
					return instance;
				}
			};
		}

		function configureContext(options) {
			// TODO: This configuration object needs to be abstracted and reused
			config = {
				pluginApi: pluginApi,
				resolvers: resolvers,
				facets: facets,
				listeners: listeners
			};

			lifecycle = new Lifecycle(config);
			resolver = new Resolver(config);

			contextHandlers = {
				init: array.delegate(options.init),
				destroy: array.delegate(options.destroy)
			};
		}

		function parseSpec(scopeDef, scopeReady) {
			var promises, componentsToCreate;

			promises = [];
			componentsToCreate = {};

			// Setup a promise for each item in this scope
			for (var name in scopeDef) {
				// An initializer may have inserted concrete components
				// into the context.  If so, they override components of the
				// same name from the input spec
				if(!(components.hasOwnProperty(name))) {
					promises.push(componentsToCreate[name] = components[name] = defer());
				}
			}

			// When all scope item promises are resolved, the scope
			// is ready. When this scope is ready, resolve the promise
			// with the objects that were created
			chain(whenAll(promises), scopeReady, components);

			return componentsToCreate;
		}

		//
		// Context Startup
		//

		function createComponents(componentsToCreate, spec) {
			// Process/create each item in scope and resolve its
			// promise when completed.
			for (var name in componentsToCreate) {
				createScopeItem(name, spec[name], components[name]);
			}
		}

		function ensureAllModulesLoaded() {
			// Once all modules have been loaded, resolve modulesReady
			whenAll(modulesToLoad, function (modules) {
				modulesReady.resolve(modules);
				modulesToLoad = undef;
			}, modulesReady.reject);
		}

		//
		// Context Destroy
		//

		function destroyContext() {
			var shutdown;

			// First destroy all child scopes
			for (var i = 0; i < _childScopes.length; i++) {
				_childScopes[i] = _childScopes[i].destroy();
			};

			// Continue processing only when all child scopes have finished
			// destroying themselves
			return when.all(_childScopes).always(function() {

				scopeDestroyed.resolve();

				// TODO: Clear out the context prototypes?

				shutdown = when.reduce(proxiedComponents, function(unused, proxied) {
					return lifecycle.shutdown(proxied);
				}, undef);

				return when(shutdown, function () {
					var i, len;

					function deleteAll(container) {
						for(var p in container) {
							delete container[p];
						}
					}

					deleteAll(components);
					deleteAll(scope);

					return when.reduce(proxiedComponents, function(p, proxied) {
						when(p, function() {
							proxied.destroy();
						});
					}, undef)
					.then(function() {
						// Free Objects
						components = scope = parent
							= resolvers = factories = facets = listeners
							= wireApi = proxiedComponents = proxiers = plugins
							= _getPluginApi = _childScopes
							= undef;

						return scopeDestroyed;

					});
				});
			});
		}

		//
		// Dynamic Component/Scope Destroy
		//

		/**
		 * This function destroyes and removes all matching components and scopes from the context,
		 * without destroying the context itself.
		 *
		 * Since this function scans the _childScopes and proxiedComponents arrays, it also assumes
		 * the additional responsibility to remove holes from the _childScopes array, because scopes
		 * can be destroyed without calling this function, leaving holes in the array.
		 *
		 * Note that due to our approach of using scopes to support namespaces, a namespace is simply
		 * the name of a scope, and destroying everything under that namespace is as simple as destroying
		 * that scope.
		 *
		 * @param name {String} name to match against components and scopes' `_origin` fields.
		 *                      Specifically, an empty string means to match all components and scopes.
		 * @returns {Promise} resolves when all matching children are destroyed, or rejects when an
		 *                    error occurs.
		 */
		function _destroyChildren(name) {
			var i, j;

			// Match the name against the `_origin` of components and scopes in this scope.
			var promises = [];

			function destroyComponent(proxy) {
				return when(lifecycle.shutdown(proxy), function() {
					// If the component is in components, remove it
					if (components[proxy._name] === proxy.target) {
						delete components[proxy._name];
					}

					return proxy.destroy();
				});
			}

			var proxyArray = components._scope._proxiedComponents;
			j = proxyArray.length - 1;
			for (i = 0; i <= j; i++) {
				if (proxyArray[i]._origin === name) {
					// This component needs to be destroyed
					promises.push(destroyComponent(proxyArray[i]));
					proxyArray[i] = proxyArray[j];
					j--;
				}
			}
			proxyArray.length = j + 1;

			var scopeArray = components._scope._childScopes;
			j = scopeArray.length - 1;
			for (i = 0; i <= j; i++) {
				if (scopeArray[i].destroy) {
					if (scopeArray[i]._origin === name) {
						// This scope needs to be destroyed
						promises.push(scopeArray[i].destroy());
					} else {
						continue;
					}
				}
				// We are here because either the scope needs to be destroyed
				// or it has already been destroyed.
				scopeArray[i] = scopeArray[j];
				j--;
			}
			scopeArray.length = j + 1;

			return when.all(promises);
		}

		//
		// Context API
		//

		// API of a wired context that is returned, via promise, to
		// the caller.  It will also have properties for all the
		// objects that were created in this scope.

		/**
		 * Resolves a reference in the current context, using any reference resolvers
		 * available in the current context
		 *
		 * @param ref {String} reference name (may contain resolver prefix, e.g. "resolver!refname"
		 */
		function apiResolveRef(ref, onBehalfOf) {
			return when(resolveRefName(ref, {}, onBehalfOf));
		}

		/**
		 * Destroys the current context
		 */
		function apiDestroy() {
			return destroy();
		}

		/**
		 * Wires a child spec with this context as its parent
		 * @param spec
		 */
		function wireChild(spec, options) {
			return createContext(spec, scopeParent, options);
		}

		//
		// Scope functions
		//

		function createPath(name, basePath) {
			var path = basePath || scope.path;

			return (path && name) ? (path + '.' + name) : name;
		}

		function createScopeItem(name, val, itemPromise) {
			// NOTE: Order is important here.
			// The object & local property assignment MUST happen before
			// the chain resolves so that the concrete item is in place.
			// Otherwise, the whole scope can be marked as resolved before
			// the final item has been resolved.
			var p = createItem(val, name, name);

			return when(p, function (resolved) {
				makeResolvable(name, resolved);
				itemPromise.resolve(resolved);
			}, chainReject(itemPromise));
		}

		/**
		 * Make a component resolvable under the given name
		 * @param name {String} name by which to allow the component to be resolved
		 * @param component {*} component
		 */
		function makeResolvable(name, component) {
			// If `name` is something like `undefined`, it doesn't make sense
			// to make the component resolvable under 'undefined'.
			// If the component is a member of an array, it also doesn't make
			// sense to make it resolvable under 'array_name[]', only to be
			// overwritten immediately by its next sibling.
			if (name && (name[name.length-1] !== ']' || name[name.length-2] !== '[')) {
				components[name] = getResolvedValue(component);
			}
		}

		/**
		 * # The _origin System #
		 *
		 * ## Purpose ##
		 *
		 * Wire's creation of components and scopes from a spec is recursive, meaning
		 * that a user's action to wire a component or scope using a spec can ultimately
		 * cause multiple components and scopes being wired in the process.
		 *
		 * When implementing dynamic component creations and destructions, it's important
		 * to be able to destroy all these components and scopes when the user later
		 * decides to destroy the component or scope he wired with that spec. This
		 * requires us to track all components and scopes that are created because of
		 * the creation of another component or scope (the "origin" of these components
		 * and scopes). The _origin system does just that.
		 *
		 * ## Design ##
		 *
		 * The system relies a new `_origin` property on all components (actually their
		 * proxies) and scopes, indicating the resolvable name of the component or scope
		 * in the same parent scope that is the cause of their creation.
		 *
		 * Note that the `_origin` of a component or scope is not necessarily the original
		 * component or scope that was explicitly wired by the user. It's the origin of
		 * the component or scope **in its parent scope**. This is easier to implement,
		 * enough for our purposes, and even enables us to do granular destruction of
		 * child components or scopes of those explicitly created by the user using a spec.
		 *
		 * ## Implementation ##
		 *
		 * The problem is how to distinguish those components and scopes that are
		 * explicitly wired and those that are wired as a result of the wiring of
		 * another component or scope.
		 *
		 * Wire provides two ways for the user to specify the names used to make these
		 * new components resolvable:
		 * 1. Through object (scope) keys in specs
		 * 2. Through arguments to the wire() call
		 *
		 * In Wire (our modified form), all calling of the wire() function from built-in
		 * plugins don't specify a name. This follows our principle that all components
		 * and scopes wire()'ed explicitly by the user must be given a name, while all
		 * those wire()'ed because of the wiring of another component or scope must not
		 * be given a name.
		 *
		 * This principle ensures that in any give scope S, all the components and scopes
		 * directly inside S that have a resolvable name are created explicitly by the user,
		 * and their `_origin` values should be themselves. On the other hand, all other
		 * components and scopes are created because of the creation of one of these resolvable
		 * components or scopes, and their `_origin` values should be one of these.
		 *
		 * To implement this formula, we simply pass an _origin value around in all relevant
		 * functions, so that when we encounter a component or scope whose name is not specified,
		 * we can use this passed _origin value as its `_origin`. On the other hand, if its
		 * name is specified, we use this name as the new _origin value.
		 *
		 * The only exception is pluginApi (the wire() function). To maintain the stability
		 * of this API (and thus compatibility with other Wire plugins), we don't require an
		 * _origin value to be passed in plugin implementations. Instead, we use special
		 * pluginApi instances that contain the correct _origin value in a closure.
		 */
		function createItem(val, name, _origin) {
			var created;

			if (resolver.isRef(val)) {
				// Reference
				created = resolveRef(val, name);

			} else if (Array.isArray(val)) {
				// Array
				created = createArray(val, name, _origin);

			} else if (object.isObject(val)) {
				// component spec, create the component
				created = realizeComponent(val, name, _origin);

			} else {
				// Plain value
				created = when.resolve(val);
			}

			return created;
		}

		function getModule(moduleId, spec) {
			var module = defer();

			scanPluginWhenLoaded(isString(moduleId) ? moduleLoader(moduleId) : moduleId, module);

			return module.promise;

			function scanPluginWhenLoaded(loadModulePromise, moduleReadyResolver) {

				var loadPromise = when(loadModulePromise, function (module) {
					return when(scanPlugin(module, spec), function() {
						chain(modulesReady, moduleReadyResolver, module);
					});
				}, moduleReadyResolver.reject);

				modulesToLoad && modulesToLoad.push(loadPromise);

			}
		}

		function scanPlugin(module, spec) {
			if (module && isFunction(module.wire$plugin) && plugins.indexOf(module.wire$plugin) === -1) {
				// Add to singleton plugins list to only allow one instance
				// of this plugin in the current context.
				plugins.push(module.wire$plugin);

				// Initialize the plugin for this context
				return when(module.wire$plugin(scopeReady.promise, scopeDestroyed.promise, spec),
					function(plugin) {
						plugin && registerPlugin(plugin);
						return module;
					}
				);
			}

			return module;
		}

		function registerPlugin(plugin) {
			addPlugin(plugin.resolvers, resolvers);
			addPlugin(plugin.factories, factories);
			addPlugin(plugin.facets, facets);

			listeners.push(plugin);

			addProxies(plugin.proxies);
		}

		function addProxies(proxiesToAdd) {
			if (!proxiesToAdd) { return; }

			var newProxiers, p, i = 0;

			newProxiers = [];
			while (p = proxiesToAdd[i++]) {
				if (proxiers.indexOf(p) < 0) {
					newProxiers.push(p);
				}
			}

			scope.proxiers = proxiers = newProxiers.concat(proxiers);
		}

		function addPlugin(src, registry) {
			var name;
			for (name in src) {
				if (registry.hasOwnProperty(name)) {
					throw new Error("Two plugins for same type in scope: " + name);
				}

				registry[name] = src[name];
			}
		}

		function createArray(arrayDef, name, _origin) {
			// Minor optimization, if it's an empty array spec, just return
			// an empty array.
			return arrayDef.length
				? when.map(arrayDef, function(item) {
					return createItem(item, name ? name + '[]' : name, _origin);
				})
				: [];
		}

		/**
		 * Fully realize a component from a spec: create, initialize, then
		 * startup.
		 * @param spec {Object} component spec
		 * @param name {String} component name
		 * @return {Promise} promise for the fully realized component
		 */
		function realizeComponent(spec, name, _origin) {

			// Look for a factory, then use it to create the object
			return when(findFactory(spec),
				function (factory) {
					var component = defer();

					if (!spec.id) {
						spec.id = name;
					}

					factory(component.resolver, spec, _getPluginApi(_origin));

					return processComponent(component, spec, name, _origin);
				},
				function () {
					// No factory found, treat object spec as a nested scope
					return createScope(spec, scope, { name: name, _origin: _origin }).then(function(context) {
						// var s = safeMixin({}, context);
						// I don't see why we shouldn't make dynamically wire()'ed scopes resolvable
						makeResolvable(name, context);
						return context;
					});
				}
			);
		}

		/**
		 * Move component through all phases of the component lifecycle up
		 * to ready.
		 * @param component {*} component or promise for a component
		 * @param spec {Object} component spec
		 * @param name {String} component name
		 * @return {Promise} promise for the component in the ready state
		 */
		function processComponent(component, spec, name, _origin) {
			return when(component, function(component) {

				return when(createProxy(component, spec, name, _origin), function(proxy) {
					return lifecycle.init(proxy);

				}).then(function(proxy) {
					// Components become resolvable after the initialization phase
					// This allows circular references to be resolved after init
					makeResolvable(name, proxy.target);
					return lifecycle.startup(proxy);

				}).then(function(proxy) {
					return proxy.target;

				});
			});
		}

		/**
		 * Select the factory plugin to use to create a component
		 * for the supplied component spec
		 * @param spec {Object} component spec
		 * @return {Promise} promise for factory, rejected if no suitable
		 *  factory can be found
		 */
		function findFactory(spec) {

			// FUTURE: Should not have to wait for all modules to load,
			// but rather only the module containing the particular
			// factory we need.  But how to know which factory before
			// they are all loaded?
			// Maybe need a special syntax for factories, something like:
			// create: "factory!whatever-arg-the-factory-takes"
			// args: [factory args here]

			function getFactory() {
				var f, factory;

				for (f in factories) {
					if (spec.hasOwnProperty(f)) {
						factory = factories[f];
						break;
					}
				}

				// Intentionally returns undefined if no factory found
				return factory;
			}

			return getFactory() || when(modulesReady, function () {
				return getFactory() || when.reject(spec);
			});
		}

		function createProxy(object, spec, _name, _origin) {
			return when(modulesReady, function() {
				var proxier, proxy, id, i;

				i = 0;

				while ((proxier = proxiers[i++]) && !(proxy = proxier(object, spec))) {}

				proxy.target = object;
				proxy.spec = spec;

				if(spec) {
					id = spec && spec.id;
					proxy.id = id;
					proxy.path = createPath(id);
					proxy._origin = _origin;
					// Resolvable name of proxy.target
					proxy._name = _name;
					proxiedComponents.push(proxy);
				}

				return proxy;
			});
		}

		/**
		 * Return a proxy for the component name, or concrete component
		 * @param nameOrComponent {String|*} if it's a string, consider it to be a component name
		 *  otherwise, consider it to be a concrete component
		 * @return {Object|Promise} proxy or promise for proxy of the component
		 */
		function getProxy(nameOrComponent, onBehalfOf) {
			return typeof nameOrComponent != 'string'
				? createProxy(nameOrComponent)
				: when(resolveRefName(nameOrComponent, {}, onBehalfOf), function(component) {
					return createProxy(component);
				});
		}

		//
		// Destroy
		//

		/**
		 * Destroy the current context.  Waits for the context to finish
		 * wiring and then immediately destroys it.
		 *
		 * @return {Promise} a promise that will resolve once the context
		 * has been destroyed
		 */
		function destroy() {
			return when(scopeReady, doDestroy, doDestroy);
		}

		//
		// Reference resolution
		//

		/**
		 * Resolves the supplied ref as a local component name, or delegates
		 * to registered resolver plugins
		 * @param ref {Object} reference object returned by resolver.parse or resolver.create
		 * @param scope {Object} scope for resolving local component names
		 * @param [onBehalfOf] {*} optional indicator of the party requesting the reference
		 * @return {Promise} a promise for the fully resolved reference value
		 */
		function doResolveRef(ref, scope, onBehalfOf) {
			var resolution = ref.resolver ? when(modulesReady, ref.resolve) : doResolveDeepRef(ref.name, scope);

			return trackInflightRef(resolution, inflightRefs, ref.name, onBehalfOf);
		}

		/**
		 * Resolves a component references, traversing one level of "." nesting
		 * if necessarily (e.g. "thing.property")
		 * @param name {String} component name or dot-separated path
		 * @param scope {Object} scope in which to resolve the reference
		 * @return {Promise} promise for the referenced component or property
		 */
		function doResolveDeepRef(name, scope) {
			var parts = name.split('.');

			if(parts.length > 2) {
				return when.reject('Only 1 "." is allowed in refs: ' + name);
			}

			return when.reduce(parts, function(scope, segment) {
				return segment in scope
					? scope[segment]
					: when.reject('Cannot resolve ref: ' + name);
			}, scope);
		}

		/**
		 * @param ref {*} any reference format supported by the registered resolver
		 * @param name {String} component name to which the the resolved value of the reference
		 *  will eventually be assigned.  Used to avoid self-circular references.
		 * @return {Promise} a promise for the fully resolved reference value
		 */
		function resolveRef(ref, name) {
			var scope;

			ref = resolver.parse(ref);
			scope = name == ref.name && parent.components ? parent.components : components;

			return doResolveRef(ref, scope, name);
		}

		/**
		 *
		 * @param refName {String} name of reference to resolve. Can be either a
		 *  component name, or a plugin-style reference, e.g. plugin!reference
		 * @param [options] {Object} additional options to pass to reference resolver
		 *  plugins if the refName requires a plugin to resolve
		 * @param [onBehalfOf] {*} optional indicator of the party requesting the reference
		 * @return {Promise} a promise for the fully resolved reference value
		 */
		function resolveRefName(refName, options, onBehalfOf) {
			return doResolveRef(resolver.create(refName, options), components, onBehalfOf);
		}

		/**
		 * Builtin reference resolver that resolves to the context-specific
		 * wire function.
		 *
		 * @param resolver {Resolver} resolver to resolve
		 */
		function wireResolver(resolver /*, name, refObj, wire*/) {
			resolver.resolve(wireApi);
		}

		//
		// Built-in Factories
		//

		/**
		 * Factory that creates either a child context, or a *function* that will create
		 * that child context.  In the case that a child is created, this factory returns
		 * a promise that will resolve when the child has completed wiring.
		 *
		 * @param resolver {Resolver} resolver to resolve with the created component
		 * @param spec {Object} portion of the spec for the component to be created
		 */
		function wireFactory(resolver, spec, wire) {
			//
			// TODO: Move wireFactory to its own module
			//
			var options, module, provide, defer, waitParent;

			options = spec.wire;

			// Get child spec and options
			if (isString(options)) {
				module = options;
			} else {
				module = options.spec;
				waitParent = options.waitParent;
				defer = options.defer;
				provide = options.provide;
			}

			function init(context) {
				if(provide) {
					return when(wire(provide), function(provides) {
						safeMixin(context.components, provides);
					});
				}
			}

			function createChild(/** {Object|String}? */ mixin) {
				var spec, config;

				spec = mixin ? [].concat(module, mixin) : module;
				config = { init: init, _origin: wire._origin };

				var child = wireChild(spec, config);
				return defer ? child
					: when(child, function(child) {
						return child.hasOwnProperty('$exports') ? child.$exports : child;
					});
			}

			if (defer) {
				// Resolve with the createChild *function* itself
				// which can be used later to wire the spec
				resolver.resolve(createChild);

			} else if(waitParent) {

				var childPromise = when(scopeReady, function() {
					// ensure nothing is passed to createChild here
					return createChild();
				});

				resolver.resolve(new ResolvedValue(childPromise));

			} else {
				when.chain(createChild(spec), resolver);

			}
		}

	} // createScope

	function getModuleLoader(context, options) {
		return options && options.require
			? createModuleLoader(options.require)
			: context.moduleLoader;
	}

	/**
	 * Given a mixed array of strings and non-strings, returns a promise that will resolve
	 * to an array containing resolved modules by loading all the strings found in the
	 * specs array as module ids
	 * @private
	 *
	 * @param specs {Array} mixed array of strings and non-strings
	 *
	 * @returns {Promise} a promise that resolves to an array of resolved modules
	 */
	function ensureAllSpecsLoaded(specs, loadModule) {
		return when.reduce(specs, function(merged, module) {
			return isString(module)
				? when(loadModule(module), function(spec) { return safeMixin(merged, spec); })
				: safeMixin(merged, module);
		}, {});
	}

	/**
	 * Add components in from to those in to.  If duplicates are found, it
	 * is an error.
	 * @param to {Object} target object
	 * @param from {Object} source object
	 */
	function safeMixin(to, from) {
		for (var name in from) {
			if (from.hasOwnProperty(name) && !(name in emptyObject)) {
				if (to.hasOwnProperty(name)) {
					throw new Error("Duplicate component name in sibling specs: " + name);
				} else {
					to[name] = from[name];
				}
			}
		}

		return to;
	}

	function isString(it) {
		return typeof it == 'string';
	}

	/**
	 * Standard function test
	 * @param it
	 */
	function isFunction(it) {
		return typeof it == 'function';
	}

	/**
	 * Helper to reject a deferred when another is rejected
	 * @param resolver {Object} resolver to reject
	 */
	function chainReject(resolver) {
		return function (err) {
			resolver.reject(err);
		};
	}

	/**
	 * Special object to hold a Promise that should not be resolved, but
	 * rather should be passed through a promise chain *as the resolution value*
	 * @param val
	 */
	function ResolvedValue(val) {
		this.value = val;
	}

	/**
	 * If it is a PromiseKeeper, return it.value, otherwise return it.  See
	 * PromiseKeeper above for an explanation.
	 * @param it anything
	 */
	function getResolvedValue(it) {
		return it instanceof ResolvedValue ? it.value : it;
	}

	/**
	 * Run the supplied async tasks in sequence, with no overlap.
	 * @param tasks {Array} array of functions
	 * @return {Promise} promise that resolves when all tasks
	 * have completed
	 */
	function sequence(tasks) {
		var args = array.fromArguments(arguments, 1);
		return when.reduce(tasks, function(context, task) {
			return when(task.apply(context, args), function() {
				return context;
			});
		}, undef);
	}

	// TODO: Start using this after compatible curl release
	// TODO: Move to somewhere more logical and modular, like lib/resolver.js
	function trackInflightRef(refPromise, inflightRefs, refName, onBehalfOf) {
		return refPromise;

		// var inflight = (onBehalfOf||'?') + ' -> ' + refName;

		// inflightRefs.push(inflight);

		// return timeout(refPromise, 1e4).then(
		// 	function(resolved) {
		// 		// Successfully resolved, remove from inflight
		// 		var ref, i = inflightRefs.length;
		// 		while(ref = inflightRefs[--i]) {
		// 			if(ref === inflight) {
		// 				inflightRefs.splice(i, 1);
		// 				break;
		// 			}
		// 		}

		// 		return resolved;
		// 	},
		// 	function(e) {
		// 		// Could not resolve in a reasonable time, warn of possible deadlocked
		// 		// circular ref
		// 		return when.reject(e == 'timed out'
		// 			? ('Possible circular ref:\n' + inflightRefs.join('\n'))
		// 			: e);
		// 	}
		// );
	}

});
})(typeof define == 'function'
	// AMD
	? define
	// CommonJS
	: function(deps, factory) {
		module.exports = factory.apply(this, [require].concat(deps.slice(1).map(function(x) {
			return require(x);
		})));
	}
);
