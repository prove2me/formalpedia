-- Prove2me | Theorems.Thm_FriedCrossing_ClusterMatrix_contDiff_trace_fin_two
-- name    : FriedCrossing.ClusterMatrix.contDiff_trace_fin_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:42:41.034863+00:00
-- url     : https://prove2.me/theorems/dc43e252-9389-5774-a451-b961f33cefbe
-- title:
--   Cluster Matrix: cont Diff trace fin two
-- statement:
--   The Cluster Matrix construction uses the cont Diff trace fin two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L110-L112
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L110-L112

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

theorem FriedCrossing.ClusterMatrix.contDiff_trace_fin_two {M : E → Matrix (Fin 2) (Fin 2) ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => M x i j) : ContDiff ℝ k fun x => (M x).trace := by sorry
