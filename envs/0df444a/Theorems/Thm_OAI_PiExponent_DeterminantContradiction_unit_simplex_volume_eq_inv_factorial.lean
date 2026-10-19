-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unit_simplex_volume_eq_inv_factorial
-- name    : OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_eq_inv_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T21:26:19.377194+00:00
-- url     : https://prove2.me/theorems/f9aa8224-73b1-443a-b034-d3ff74371222
-- title:
--   Closed formula for unit simplex volume
-- statement:
--   The volume of the nonnegative unit simplex in dimension n is the reciprocal of n factorial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.unit_simplex_volume_eq_inv_factorial (n : ℕ) :
    (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal =
      1 / (Nat.factorial n : ℝ) := by sorry
