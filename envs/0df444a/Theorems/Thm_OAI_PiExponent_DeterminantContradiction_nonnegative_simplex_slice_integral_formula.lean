-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonnegative_simplex_slice_integral_formula
-- name    : OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_slice_integral_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:29:22.811852+00:00
-- url     : https://prove2.me/theorems/4eeb500d-ff51-4eeb-a681-fc814e2df9cb
-- title:
--   Integral of nonnegative simplex slice volumes
-- statement:
--   For a nonnegative cutoff, the integral of the m-dimensional slice volumes from zero to U equals U to the (m+1)-st power divided by (m+1) factorial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_slice_integral_formula (m : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    ∫ t in (0 : ℝ)..U,
      (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ U - t}).toReal =
      (U ^ (m + 1)) / (Nat.factorial (m + 1) : ℝ) := by sorry
