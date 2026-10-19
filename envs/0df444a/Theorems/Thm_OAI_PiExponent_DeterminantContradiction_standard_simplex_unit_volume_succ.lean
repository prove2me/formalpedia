-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_unit_volume_succ
-- name    : OAI.PiExponent.DeterminantContradiction.standard_simplex_unit_volume_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:19:48.126704+00:00
-- url     : https://prove2.me/theorems/90713838-e1bb-413f-9b6c-254ea94fbdc8
-- title:
--   Simplex volume slicing recurrence
-- statement:
--   In every dimension m, slicing the unit standard simplex by its last coordinate gives the next-dimensional volume as the current volume divided by m+1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.standard_simplex_unit_volume_succ
    (m : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (m + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ (1 : ℝ)}) =
      ENNReal.toReal (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ (1 : ℝ)}) / (m + 1 : ℝ) := by sorry
