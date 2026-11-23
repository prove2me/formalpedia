-- Prove2me | Theorems.Thm_NoHair_static_negative_sheet_pole_from_lapse_monopole
-- name    : NoHair.static_negative_sheet_pole_from_lapse_monopole
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:53:47.334937+00:00
-- url     : https://prove2.me/theorems/44bd72b5-f3f4-462e-a954-9b30ca77f225
-- title:
--   The lapse monopole determines the continuous metric at the compactified negative end
-- statement:
--   Under unit Euclidean inversion the compactified negative-sheet metric tends to $(\mu/2)^4\delta$ if $r(1-N)$ tends to $\mu$. The angular dependence in the differential of inversion is an orthogonal reflection. Conjugation preserves the Euclidean metric and its effect on the asymptotically vanishing metric error is uniformly controlled. Thus a positive monopole yields a nondegenerate continuous pole metric in this chart.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154. https://doi.org/10.1007/BF00770326. Here the negative sheet uses unit Euclidean inversion and the coefficient of the inverse-radius term of the lapse.

import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter
open scoped Topology ContDiff

theorem NoHair.static_negative_sheet_pole_from_lapse_monopole (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) (μ : ℝ) (hμ : HasStaticLapseMonopole N μ) :
    HasContinuousStaticPole N h μ := by
  sorry
