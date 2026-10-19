-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_eq_inv_factorial
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_eq_inv_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T21:49:19.82589+00:00
-- url     : https://prove2.me/theorems/bac6f1de-0de0-48c9-a7c9-e25f1d7a9725
-- title:
--   Unit simplex volume formula
-- statement:
--   The volume of the nonnegative unit simplex in n coordinates is the reciprocal of n factorial, including the zero-dimensional case.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_eq_inv_factorial (n : ℕ) :
    (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal =
      (Nat.factorial n : ℝ)⁻¹ := by sorry
