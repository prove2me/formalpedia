-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_sum_lower_bound_of_exp_decomp
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_sum_lower_bound_of_exp_decomp
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T13:23:58.747589+00:00
-- url     : https://prove2.me/theorems/febea19f-a8bb-433e-b270-43bd0dc69689
-- title:
--   Weighted degree is additive across exponent decompositions
-- statement:
--   For any real weights, if an exponent vector is the sum of n factor exponent vectors and every factor has weighted degree at least B, then the total weighted degree is at least n times B.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_sum_lower_bound_of_exp_decomp
    {m n : ℕ} (wt : Fin (m + 1) → ℝ) (B : ℝ)
    (b : Fin n → Fin (m + 1) → ℕ) (a : Fin (m + 1) → ℕ)
    (hdecomp : (∑ i : Fin n, InterpolationMatrix.exponentVector (b i)) =
      InterpolationMatrix.exponentVector a)
    (hb : ∀ i : Fin n,
      B ≤ ∑ k : Fin (m + 1), wt k * (b i k : ℝ)) :
    (n : ℝ) * B ≤ ∑ k : Fin (m + 1), wt k * (a k : ℝ) := by sorry
