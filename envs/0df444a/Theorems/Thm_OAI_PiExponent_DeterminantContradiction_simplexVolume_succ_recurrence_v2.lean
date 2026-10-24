-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_recurrence_v2
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_recurrence_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:54:14.106757+00:00
-- url     : https://prove2.me/theorems/b146a0f4-ab3c-4001-bcff-3f37235a4f09
-- title:
--   Simplex volume successor recurrence
-- statement:
--   The volume of the nonnegative unit simplex in dimension n+1 is its dimension-n volume divided by n+1. Slice by the last coordinate t; each section is a scaled dimension-n simplex, and integrating its volume factor (1−t)^n over [0,1] yields 1/(n+1). This includes n = 0.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_recurrence_v2 (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (n + 1 : Real)) *
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} := by sorry
