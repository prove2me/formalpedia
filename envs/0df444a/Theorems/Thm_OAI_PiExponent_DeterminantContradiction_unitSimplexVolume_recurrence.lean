-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_recurrence
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_recurrence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:19:47.902582+00:00
-- url     : https://prove2.me/theorems/0eabd1b3-9bd4-4704-b5b8-22125c26c35b
-- title:
--   Volume recurrence for the unit coordinate simplex
-- statement:
--   The volume of the successor-dimensional unit coordinate simplex is the current simplex volume divided by n+1. Slice by the final coordinate, apply Fubini, and scale each lower-dimensional slice by 1−t.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_recurrence (n : Nat) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      ENNReal.ofReal (1 / (n + 1 : Real)) *
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1} := by sorry
