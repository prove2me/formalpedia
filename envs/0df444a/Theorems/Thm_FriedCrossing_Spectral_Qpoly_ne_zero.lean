-- Prove2me | Theorems.Thm_FriedCrossing_Spectral_Qpoly_ne_zero
-- name    : FriedCrossing.Spectral.Qpoly_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:43:31.411286+00:00
-- url     : https://prove2.me/theorems/a8a14e3f-5811-512a-8ebd-2153fc340788
-- title:
--   Spectral: Qpoly ne zero
-- statement:
--   The Spectral construction uses the Qpoly ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L617-L620
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L617-L620

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem FriedCrossing.Spectral.Qpoly_ne_zero (e₁ e₂ : ℝ) : Qpoly e₁ e₂ ≠ 0 := by sorry
