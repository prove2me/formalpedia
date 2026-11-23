-- Prove2me | Theorems.Thm_NoHair_bounded_differential_punctured_ball_has_unique_limit
-- name    : NoHair.bounded_differential_punctured_ball_has_unique_limit
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T12:01:18.051795+00:00
-- url     : https://prove2.me/theorems/b384ac5c-b53f-4ba2-84f2-e3c170ac6208
-- title:
--   A Riemannian map with bounded differential on a punctured three-ball has a unique limit in the completion
-- statement:
--   For two points in a small ball about the puncture, join each by a segment to a third point outside their linear span. The two segments avoid the origin and lie in the ball. The derivative bound controls their Riemannian lengths and bounds the oscillation by four times the radius times the derivative bound. Completeness of the metric completion gives a common limit at the puncture.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.bounded_differential_punctured_ball_has_unique_limit (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] (f : ADMPoint → Q) (r K : ℝ) (hr : 0<r) (hk : 0<K)
    (sm : ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) 1 f (Metric.ball 0 r ∩ ({0}:Set ADMPoint)ᶜ))
    (bd : ∀ x ∈ Metric.ball (0:ADMPoint) r ∩ ({0}:Set ADMPoint)ᶜ, ∀ v : ADMPoint,
      ‖mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) f x v‖ ≤ K*‖v‖) :
    ∃ p : UniformSpace.Completion Q, Tendsto (fun x => (f x : UniformSpace.Completion Q))
      (𝓝[≠] (0:ADMPoint)) (𝓝 p) := by sorry
