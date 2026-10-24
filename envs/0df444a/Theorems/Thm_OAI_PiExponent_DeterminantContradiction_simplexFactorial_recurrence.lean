-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexFactorial_recurrence
-- name    : OAI.PiExponent.DeterminantContradiction.simplexFactorial_recurrence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:59:44.144369+00:00
-- url     : https://prove2.me/theorems/dde16ea4-8b28-4969-aeb5-09514c41b804
-- title:
--   Scalar factorial recurrence for simplex volume
-- statement:
--   The real reciprocal factors 1/(n+1) and 1/n! multiply, after embedding in ENNReal, to 1/(n+1)!.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem OAI.PiExponent.DeterminantContradiction.simplexFactorial_recurrence (n : Nat) :
    ENNReal.ofReal (1 / (n + 1 : Real)) *
        ENNReal.ofReal (1 / (Nat.factorial n : Real)) =
      ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by sorry
