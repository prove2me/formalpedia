-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonnegative_simplex_volume_formula
-- name    : OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:29:09.875032+00:00
-- url     : https://prove2.me/theorems/32f3075d-4f82-4cd1-9c01-2816f279df3c
-- title:
--   Volume formula for a nonnegative simplex
-- statement:
--   For a nonnegative cutoff, the volume of the nonnegative simplex in dimension k equals U to the k-th power divided by k factorial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_formula (k : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    (MeasureTheory.volume
      {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ U}).toReal =
      (U ^ k) / (Nat.factorial k : ℝ) := by sorry
