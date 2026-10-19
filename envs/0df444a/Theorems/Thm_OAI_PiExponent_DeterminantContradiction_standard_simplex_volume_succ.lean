-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_volume_succ
-- name    : OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T22:16:10.604067+00:00
-- url     : https://prove2.me/theorems/6c98f6ef-c2bf-4b56-be7b-9f078efe112c
-- title:
--   Successor recurrence for standard simplex volume
-- statement:
--   The volume in dimension n+1 equals the volume in dimension n divided by n+1. Slicing at one coordinate and integrating the volumes of the scaled n-dimensional sections gives this recurrence, including n = 0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_succ
    (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (1 : ℝ)}) =
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ENNReal.toReal (MeasureTheory.volume
          {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) := by sorry
