-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_volume_closed_form
-- name    : OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_closed_form
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:04:00.473627+00:00
-- url     : https://prove2.me/theorems/78225883-d038-4e4a-b822-43711e20b4a1
-- title:
--   Closed-form volume of the standard simplex
-- statement:
--   The volume of the nonnegative unit simplex in dimension n is 1 divided by n factorial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.standard_simplex_volume_closed_form
    (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) =
      1 / ((Nat.factorial n : ℕ) : ℝ) := by sorry
