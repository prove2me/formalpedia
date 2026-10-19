-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_scale
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:46:49.666618+00:00
-- url     : https://prove2.me/theorems/8bbf4eec-1acc-4e22-876d-7f4e363f2594
-- title:
--   Homogeneity of nonnegative simplex volume
-- statement:
--   The volume of the nonnegative simplex with cutoff U is U^k times the volume of the unit simplex in dimension k.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_scale (k : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    (MeasureTheory.volume
      {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ U}).toReal =
      (U ^ k) * (MeasureTheory.volume
        {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin k, x i ≤ 1}).toReal := by sorry
