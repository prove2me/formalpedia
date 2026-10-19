-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_factorial
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T22:04:46.767639+00:00
-- url     : https://prove2.me/theorems/b4c2f315-f4fe-49bc-9f39-46319dd88150
-- title:
--   Unit simplex volume closed form
-- statement:
--   For every natural dimension n, the volume of the set of nonnegative coordinates whose sum is at most one is the reciprocal of n factorial. The statement includes dimension zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_factorial (n : ℕ) :
    (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal =
      1 / (Nat.factorial n : ℝ) := by sorry
