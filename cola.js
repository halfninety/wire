/** @license MIT License (c) copyright B Cavalier & J Hann */

/**
 * wire/cola plugin
 *
 * wire is part of the cujo.js family of libraries (http://cujojs.com/)
 *
 * Licensed under the MIT License at:
 * http://www.opensource.org/licenses/mit-license.php
 */

(function(define) {
define(['when', 'when/apply'],
function(when, apply) {

	var isArray, undef, slice;

	function querySelector (selector, node) {
		return node.querySelector(selector);
	}

	isArray = Array.isArray || function(it) {
		return Object.prototype.toString.call(it) == '[object Array]';
	};

	slice = Array.prototype.slice;

	function createPropertyTransform(transforms, wire) {

		// Could optimize the single function/string case here
		// by avoiding the when.reduce.  If wire spec parsing perf
		// ever becomes a problem, we can optimize a bit here.

		if(!isArray(transforms)) {
			transforms = [transforms];
		}

		return when.reduce(transforms,
			function(txList, txSpec) {
				var name;

				if(typeof txSpec == 'function') {
					return txSpec;
				}

				// Determine the name of the transform and try
				// to resolve it as a component in the current
				// wire spec
				if(typeof txSpec == 'string') {
					name = txSpec;
				} else {
					for(name in txSpec) {
						if(name != 'inverse') break;
					}
				}

				return when(wire.resolveRef(name),
					function(transform) {
						txList.push(function() {
							var args = slice.call(arguments);
							return transform.apply(undef, args.concat(txSpec[name]));
						});
						return txList;
					}
				);
			}, [])
		.then(
			function(txList) {
				return txList.length > 1 ? compose(txList) : txList[0];
			}
		);
	}

	function setupBinding(bindingSpecs, name, wire) {
		var bindingSpec, binding;

		bindingSpec = copyOwnProps(bindingSpecs[name]);
		binding = {
			name: name,
			spec: bindingSpec
		};

		return bindingSpec.transform
			? when(createPropertyTransform(bindingSpec.transform, wire),
				function(propertyTransform) {
					binding.spec.transform = propertyTransform;
					return binding;
				})
			: binding;
	}

	function setupBindings(bindingSpecs, wire) {
		var promises = [];

		for(var name in bindingSpecs) {
			if(bindingSpecs.hasOwnProperty(name)) {
				promises.push(setupBinding(bindingSpecs, name, wire));
			}
		}

		return when.reduce(promises, function(bindings, bindingSpec) {
			bindings[bindingSpec.name] = bindingSpec.spec;
			return bindings;
		}, {});
	}

	function bindFacet(resolver, facet, wire) {
		var options, target, promise;

		target = facet.target;
		options = facet.options;

		promise = when(wire(options), function(options) {
			var p, hubOptions, to, bindings;

			to = options.to;
			if(!to) {
				throw new Error('wire/cola: "to" must be specified');
			}

			bindings = options.bindings;

			delete options.to;
			delete options.bindings;

			hubOptions = copyOwnProps(options);

			if(!hubOptions.querySelector) {
				hubOptions.querySelector = querySelector;
			}

			return when(setupBindings(bindings, wire),
				function(bindings) {
					hubOptions.bindings = copyOwnProps(bindings);
					to.addSource(target, hubOptions);
					return target; // doesn't matter what we return here
				}
			);
		});

		when.chain(promise, resolver);
	}

	function copyOwnProps(src) {
		var dup, p;

		dup = {};
		for(p in src) {
			if(src.hasOwnProperty(p)) {
				dup[p] = src[p];
			}
		}

		return dup;
	}

	return {
		wire$plugin: function(ready, destroyed, pluginOptions) {

			return {
				facets: {
					bind: {
						ready: bindFacet
					}
				}
			};
		}
	};
});

})(typeof define == 'function'
	// use define for AMD if available
	? define
	: function(deps, factory) {
		module.exports = factory.apply(this, deps.map(function(x) {
			return require(x);
		}));
	}
);
