-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplexVolume_succ
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplexVolume_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:12:25.276758+00:00
-- url     : https://prove2.me/theorems/00a6030d-edb0-4298-8588-d00c704def7f
-- title:
--   Successor recurrence for standard simplex volume
-- statement:
--   The real volume of the dimension-(n+1) nonnegative unit simplex equals the dimension-n volume divided by n+1, by slicing at the last coordinate and integrating the scaled slice volumes.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.standardSimplexVolume_succ (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (1 : ℝ)}) =
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) / (n + 1 : ℝ) := by sorry
