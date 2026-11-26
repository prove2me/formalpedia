-- Prove2me | Theorems.Thm_FriedCrossing_Regularity_differentiable_of_contDiff
-- name    : FriedCrossing.Regularity.differentiable_of_contDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:41:02.099554+00:00
-- url     : https://prove2.me/theorems/0d248d20-7945-4e3e-be7a-1887c74c83eb
-- title:
--   Regularity: differentiable of cont Diff
-- statement:
--   The Regularity construction uses the differentiable of cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L168-L171
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L168-L171

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity

theorem FriedCrossing.Regularity.differentiable_of_contDiff {f : ℝ → ℝ → ℝ} {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (hf : ContDiff ℝ n fun q : ℝ × ℝ => f q.1 q.2) :
    Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2 := by sorry
