-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unit_simplex_measurable
-- name    : OAI.PiExponent.DeterminantContradiction.unit_simplex_measurable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:01:45.920149+00:00
-- url     : https://prove2.me/theorems/3494c245-1ea2-46ce-93ce-dc7076b878ae
-- title:
--   Measurability of the unit simplex
-- statement:
--   The nonnegative unit simplex in the finite-dimensional real coordinate space is measurable.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.unit_simplex_measurable
    (n : ℕ) :
    MeasurableSet
      ({x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)} : Set (Fin n → ℝ)) := by sorry
