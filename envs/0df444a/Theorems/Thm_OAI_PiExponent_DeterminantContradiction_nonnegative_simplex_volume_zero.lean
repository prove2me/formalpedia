-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonnegative_simplex_volume_zero
-- name    : OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:05:30.654078+00:00
-- url     : https://prove2.me/theorems/d53d07c5-7b0b-4b4b-a032-55812c8a526a
-- title:
--   Zero-dimensional nonnegative simplex volume
-- statement:
--   For every nonnegative cutoff, the zero-dimensional nonnegative simplex has volume one, equal to the formula with dimension zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_zero
    (U : ℝ) (hU : 0 ≤ U) :
    (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ U}).toReal =
      U ^ 0 / (Nat.factorial 0 : ℝ) := by sorry
