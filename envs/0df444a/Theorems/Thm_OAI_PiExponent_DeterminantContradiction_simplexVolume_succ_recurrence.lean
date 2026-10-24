-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_recurrence
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_recurrence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:12:20.438792+00:00
-- url     : https://prove2.me/theorems/424a3c01-2483-46bd-9c6c-1f939be55564
-- title:
--   Simplex volume successor recurrence
-- statement:
--   The volume of the standard nonnegative simplex in dimension n+1 is the volume in dimension n multiplied by 1/(n+1). Obtain this by integrating the last-coordinate slices; each slice at t is a dilation by 1−t. The statement includes n = 0.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_recurrence (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by sorry
