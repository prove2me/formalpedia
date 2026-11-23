-- Prove2me | Theorems.Thm_NoHair_reflected_negative_static_end_adds_one_metric_completion_point
-- name    : NoHair.reflected_negative_static_end_adds_one_metric_completion_point
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:01:09.116838+00:00
-- url     : https://prove2.me/theorems/2ee7e5ad-bd4d-417c-8c76-bf5a070daf39
-- title:
--   Every sequence escaping the reflected negative end converges to the same new metric-completion point
-- statement:
--   Unit inversion changes the inverse-fourth-power metric upper bound into a uniform bound on the differential of the reflected negative chart. Its image has a common limit in the metric completion as the inversion coordinate approaches zero. The signed lapse tends to minus one there. Since the signed lapse is continuous and strictly larger than minus one at every point of the reflected manifold, the limit is a genuinely new point.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.reflected_negative_static_end_adds_one_metric_completion_point (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h) :
    ∃ p : UniformSpace.Completion d.carrier, (∀ q : d.carrier, (q : UniformSpace.Completion d.carrier) ≠ p) ∧
      Tendsto (fun x : ADMPoint => ((d.side false).symm x : UniformSpace.Completion d.carrier))
        (cocompact ADMPoint) (𝓝 p) := by sorry
