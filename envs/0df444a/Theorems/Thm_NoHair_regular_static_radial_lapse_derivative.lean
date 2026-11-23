-- Prove2me | Theorems.Thm_NoHair_regular_static_radial_lapse_derivative
-- name    : NoHair.regular_static_radial_lapse_derivative
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T12:14:06.222802+00:00
-- url     : https://prove2.me/theorems/374b6998-ffe1-43e7-bdb3-536256334fa6
-- title:
--   Uniform radial derivative of the static lapse monopole
-- statement:
--   The radial derivative of a regular static lapse has the same leading coefficient as its inverse-radius defect. Equivalently, the normalized radial derivative r² ∂ᵣN converges to μ uniformly on spheres. The second derivative falloff controls the error of taking a radial difference quotient.
-- source:
--   R. Beig and W. Simon, Proof of a multipole conjecture due to Geroch, Comm. Math. Phys. 78 (1980), 75–82, https://doi.org/10.1007/BF01941970. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. These statements concern the lapse and its radial coordinate near the compactified end.

import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff

theorem NoHair.regular_static_radial_lapse_derivative (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) (μ : ℝ) (hm : HasStaticLapseMonopole N μ) :
    Tendsto (fun x : ADMPoint => ‖x‖ * fderiv ℝ N x x) (cocompact ADMPoint) (𝓝 μ) := by
  sorry
