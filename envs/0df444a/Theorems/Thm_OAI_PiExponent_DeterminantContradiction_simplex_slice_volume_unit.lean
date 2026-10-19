-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_volume_unit
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_slice_volume_unit
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T21:14:18.629329+00:00
-- url     : https://prove2.me/theorems/66611c67-ef17-4f23-989d-d3233d3ca317
-- title:
--   Volume of the unit nonnegative simplex
-- statement:
--   The unit simplex in m real coordinates has volume 1 divided by m factorial, including m = 0. Induct on m by slicing along one coordinate; integrate the fiber length over the lower-dimensional simplex to obtain the factorial recurrence.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_slice_volume_unit (m : ℕ) :
    (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ 1}).toReal =
      (1 : ℝ) / (Nat.factorial m : ℝ) := by sorry
