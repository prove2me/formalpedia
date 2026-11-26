-- Prove2me | Theorems.Thm_FriedCrossing_Regularity_bound_on_square
-- name    : FriedCrossing.Regularity.bound_on_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:43:05.295821+00:00
-- url     : https://prove2.me/theorems/9f2c06fe-40f3-43e5-8fec-8a4405c0ddba
-- title:
--   Regularity: bound on square
-- statement:
--   A continuous function is bounded on the unit square.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L195-L205
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L195-L205

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity

theorem FriedCrossing.Regularity.bound_on_square {g : ℝ → ℝ → ℝ} (hg : Continuous fun q : ℝ × ℝ => g q.1 q.2) :
    ∃ K : ℝ, 0 < K ∧ ∀ θ τ : ℝ, |θ| < 1 → |τ| < 1 → |g θ τ| ≤ K := by sorry
