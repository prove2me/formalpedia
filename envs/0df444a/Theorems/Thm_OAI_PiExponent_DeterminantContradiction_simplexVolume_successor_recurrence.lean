-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_successor_recurrence
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_successor_recurrence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T03:02:16.725441+00:00
-- url     : https://prove2.me/theorems/40144fec-97de-41fb-ba0a-37b2c9e6710b
-- title:
--   Unit simplex volume recurrence
-- statement:
--   The real volume of the nonnegative unit simplex in dimension n+1 is the dimension-n volume divided by n+1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_successor_recurrence (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (1 : ℝ)}) =
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) /
      (n + 1 : ℝ) := by sorry
