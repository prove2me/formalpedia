-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_slice_recurrence
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_slice_recurrence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:02:46.376134+00:00
-- url     : https://prove2.me/theorems/a977fdf1-49a2-4c5d-bc6c-82ce82d08a98
-- title:
--   Unit simplex volume recurrence by slicing
-- statement:
--   The volume of the unit coordinate simplex in dimension `n + 1` is the dimension-`n` volume times `1/(n+1)`, obtained by integrating its last-coordinate sections.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_slice_recurrence (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by sorry
