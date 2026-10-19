-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_volume_factorial_formula
-- name    : OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_factorial_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:39:52.360403+00:00
-- url     : https://prove2.me/theorems/c22931d5-bd9d-493a-91d9-797d94d16d0b
-- title:
--   Standard simplex volume formula
-- statement:
--   For every natural number n, the real-valued volume of the standard simplex in ℝⁿ, defined by nonnegative coordinates whose sum is at most one, is 1/n!.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_factorial_formula
    (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) =
      1 / (Nat.factorial n : ℝ) := by sorry
