-- Prove2me | Theorems.Thm_NoHair_kerr_inner_horizon_global_hyperbolicity
-- name    : NoHair.kerr_inner_horizon_global_hyperbolicity
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:58:47.43535+00:00
-- url     : https://prove2.me/theorems/34fb3c8d-0647-427f-9176-cd18adb0b610
-- title:
--   Global hyperbolicity above the inner Kerr horizon
-- statement:
--   The ingoing Kerr region $1<r$ for mass $5/2$ and spin $2$ is globally hyperbolic in the mission's curve-based sense. This includes both the usual exterior $r>4$ and the trapped shell $1<r<4$. The coordinate time is temporal, and causal diamonds avoid the inner horizon and remain in bounded coordinate sets. Compactness concerns the entire diamond for every pair of endpoints in this open region.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction, §§4–5 and 9, in particular equations (107)–(115), https://arxiv.org/abs/0706.0622. E. Minguzzi, Lorentzian causality theory, Living Reviews in Relativity 22 (2019) 3, https://doi.org/10.1007/s41114-019-0019-x. These statements apply the causal structure to the formal choice of inner-horizon end.

import Definitions.Def_NoHair_kerrNewmanTimeDirection

open NoHair Set

theorem NoHair.kerr_inner_horizon_global_hyperbolicity :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    IsGloballyHyperbolicOn g T A := by
  sorry
