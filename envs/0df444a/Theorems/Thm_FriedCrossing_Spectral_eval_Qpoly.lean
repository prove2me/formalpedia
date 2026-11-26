-- Prove2me | Theorems.Thm_FriedCrossing_Spectral_eval_Qpoly
-- name    : FriedCrossing.Spectral.eval_Qpoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:50:57.681945+00:00
-- url     : https://prove2.me/theorems/f09dbced-9701-5b57-b428-be955a2e72dd
-- title:
--   Spectral: eval Qpoly
-- statement:
--   The Spectral construction uses the eval Qpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L614-L615
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L614-L615

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix

theorem FriedCrossing.Spectral.eval_Qpoly (e₁ e₂ z : ℝ) : (Qpoly e₁ e₂).eval z = z ^ 2 - e₁ * z + e₂ := by sorry
