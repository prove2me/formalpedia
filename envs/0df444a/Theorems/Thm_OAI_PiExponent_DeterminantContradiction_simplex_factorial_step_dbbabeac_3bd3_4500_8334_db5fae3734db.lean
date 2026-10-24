-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_factorial_step_dbbabeac_3bd3_4500_8334_db5fae3734db
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_factorial_step_dbbabeac_3bd3_4500_8334_db5fae3734db
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:47:34.200221+00:00
-- url     : https://prove2.me/theorems/f074b2f4-1b09-4e5e-842e-c3d5c0d35a3e
-- title:
--   Factorial recurrence in ENNReal
-- statement:
--   The factorial recurrence gives the scalar identity needed after applying the volume formula and evaluating the integral. It holds at n = 0 as well; an independent proof uses Nat.factorial_succ and the nonnegativity of the reciprocal factors before applying ENNReal.ofReal multiplication.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.simplex_factorial_step_dbbabeac_3bd3_4500_8334_db5fae3734db (n : Nat) :
    ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by sorry
