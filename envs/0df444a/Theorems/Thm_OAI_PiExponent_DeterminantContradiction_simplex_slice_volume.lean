-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_volume
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_slice_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:46:01.811355+00:00
-- url     : https://prove2.me/theorems/db7e2d98-c6e8-4e1b-b0f4-413779d847be
-- title:
--   Volume of a nonnegative simplex
-- statement:
--   For a nonnegative real cutoff a, the volume of the m-dimensional region with nonnegative coordinates and coordinate sum at most a is a^m divided by m factorial, including the zero-dimensional case.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_slice_volume (m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ a}).toReal =
      (a ^ m) / (Nat.factorial m : ℝ) := by sorry
