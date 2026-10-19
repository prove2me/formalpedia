-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_succ
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T22:01:27.988185+00:00
-- url     : https://prove2.me/theorems/26b11606-0f22-43a3-b52d-261961725007
-- title:
--   Unit simplex volume recurrence
-- statement:
--   The unit simplex volume in dimension `n + 1` is the dimension-`n` volume divided by `n + 1`. Slicing at the first coordinate gives a scaled lower-dimensional simplex, and integrating its section volumes yields this factor.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_succ (n : ℕ) :
    (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ 1}).toReal =
      (MeasureTheory.volume
        {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal / ((n + 1 : ℕ) : ℝ) := by sorry
