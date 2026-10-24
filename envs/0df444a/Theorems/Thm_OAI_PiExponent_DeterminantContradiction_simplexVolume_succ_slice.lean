-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_slice
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_slice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:37:34.36916+00:00
-- url     : https://prove2.me/theorems/dbbabeac-3bd3-4500-8334-db5fae3734db
-- title:
--   Slice formula for successor simplex volume
-- statement:
--   The volume of the (n + 1)-coordinate unit simplex is the n-coordinate simplex volume multiplied by the integral of the n-dimensional section scaling factor over the last coordinate.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_slice (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by sorry
