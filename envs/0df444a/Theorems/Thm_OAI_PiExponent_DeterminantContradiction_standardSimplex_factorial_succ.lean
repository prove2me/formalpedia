-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_factorial_succ
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_factorial_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:34:46.268057+00:00
-- url     : https://prove2.me/theorems/a1b9b338-1365-4e5e-8477-9a7edb7141ee
-- title:
--   Factorial form of the volume recurrence
-- statement:
--   The factorial recurrence and the ENNReal coercions turn the volume recurrence into the desired expression at the successor dimension.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_factorial_succ (n : Nat) :
    ENNReal.ofReal (1 / (n.factorial : Real)) / (n + 1 : ENNReal) =
      ENNReal.ofReal (1 / ((n + 1).factorial : Real)) := by sorry
