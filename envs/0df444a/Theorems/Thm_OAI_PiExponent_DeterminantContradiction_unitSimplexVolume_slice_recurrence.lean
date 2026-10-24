-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_slice_recurrence
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_slice_recurrence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:52:59.886992+00:00
-- url     : https://prove2.me/theorems/4b8ad664-0b24-434c-8d18-c4c851118f5f
-- title:
--   Successor recurrence for unit simplex volume
-- statement:
--   The volume of the unit simplex in dimension n+1 is the volume in dimension n multiplied by the integral of (1-t)^n from 0 to 1. This follows by slicing along the last coordinate and scaling each n-dimensional fiber.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_slice_recurrence (n : Nat) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (Finset.univ.sum fun i : Fin n => x i) ≤ 1} *
        ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by sorry
