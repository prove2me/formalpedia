-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_det_le_permutation_sum
-- name    : OAI.PiExponent.LiteralAnalytic.norm_det_le_permutation_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T10:26:35.251672+00:00
-- url     : https://prove2.me/theorems/9a088589-7f85-4dfe-a344-115b3639a7a0
-- title:
--   Determinant norm bounded by its permutation expansion
-- statement:
--   For a finite square complex matrix, the determinant norm is at most the sum over permutations of the products of the selected entry norms. Applying this to `choiceMatrix` connects the analytic estimate to the target determinant.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Tactic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.norm_det_le_permutation_sum
    {α : Type*} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) :
    ‖M.det‖ ≤ ∑ σ : Equiv.Perm α, ∏ i : α, ‖M i (σ i)‖ := by sorry
