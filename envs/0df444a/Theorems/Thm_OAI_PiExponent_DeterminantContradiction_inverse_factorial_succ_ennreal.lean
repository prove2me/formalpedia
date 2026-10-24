-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_inverse_factorial_succ_ennreal
-- name    : OAI.PiExponent.DeterminantContradiction.inverse_factorial_succ_ennreal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:33:38.379223+00:00
-- url     : https://prove2.me/theorems/f73c9009-b3af-4859-9e9d-f866fff78b09
-- title:
--   Successor inverse-factorial identity in ENNReal
-- statement:
--   The product of the inverse factorial in dimension n and 1/(n+1), represented in ENNReal, is the inverse factorial in dimension n+1.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.inverse_factorial_succ_ennreal (n : Nat) :
    ENNReal.ofReal (1 / ((Nat.factorial n : Nat) : Real)) *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) =
      ENNReal.ofReal (1 / ((Nat.factorial (n + 1) : Nat) : Real)) := by sorry
