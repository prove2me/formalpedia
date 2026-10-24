-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_factorial_ennreal_step
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_ennreal_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:12:39.918464+00:00
-- url     : https://prove2.me/theorems/162f6a7b-db42-4d47-a85b-e296069fcceb
-- title:
--   Factorial successor step in ENNReal
-- statement:
--   Convert the product of the reciprocal n! and reciprocal n+1 in ENNReal to the reciprocal of (n+1)!, using positivity, the multiplicative rule for `ENNReal.ofReal`, and the factorial successor identity.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_ennreal_step (n : Nat) :
    ENNReal.ofReal (1 / (Nat.factorial n : Real)) *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) =
      ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by sorry
