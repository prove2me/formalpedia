-- Prove2me | Theorems.Thm_NoHair_regular_static_lapse_positive_monopole
-- name    : NoHair.regular_static_lapse_positive_monopole
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:53:47.625596+00:00
-- url     : https://prove2.me/theorems/7be07d78-203f-4295-bfa7-c64d030c3d85
-- title:
--   Positive monopole coefficient of the lapse on a regular three-dimensional static end
-- statement:
--   For an asymptotically Euclidean regular static vacuum end with a compact nondegenerate horizon, the rescaled lapse defect $r(1-N)$ has a strictly positive, direction-independent limit at infinity. This step requires the static equations and nondegeneracy, in addition to the coordinate falloff.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154. https://doi.org/10.1007/BF00770326. Here the negative sheet uses unit Euclidean inversion and the coefficient of the inverse-radius term of the lapse.

import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter
open scoped Topology ContDiff

theorem NoHair.regular_static_lapse_positive_monopole (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ μ : ℝ, 0 < μ ∧ HasStaticLapseMonopole N μ := by
  sorry
