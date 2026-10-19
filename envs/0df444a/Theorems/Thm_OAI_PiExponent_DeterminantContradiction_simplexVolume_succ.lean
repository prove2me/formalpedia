-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:33:13.279015+00:00
-- url     : https://prove2.me/theorems/c494cfb9-e39a-49dc-a649-51a198931ce8
-- title:
--   Unit simplex volume dimension recurrence
-- statement:
--   The real volume of the nonnegative unit simplex in dimension n+1 is the dimension-n volume divided by n+1. Slicing by the last coordinate reduces each slice to a scaled dimension-n simplex; Fubini, the scaling law, and integration over the slice parameter yield this recurrence. At n=0 it says the unit interval has volume one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_succ (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (1 : ℝ)}) =
    ((n + 1 : ℕ) : ℝ)⁻¹ * ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) := by sorry
