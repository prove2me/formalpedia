-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_intervalIntegral_one_sub_pow
-- name    : OAI.PiExponent.DeterminantContradiction.intervalIntegral_one_sub_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:23:57.966517+00:00
-- url     : https://prove2.me/theorems/1f70e445-2881-48ce-b585-e99f8cf71dbd
-- title:
--   Integral of a power of one minus t
-- statement:
--   For every natural n, the integral of (1−t)^n from 0 to 1 is 1/(n+1).

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem OAI.PiExponent.DeterminantContradiction.intervalIntegral_one_sub_pow (n : Nat) :
    ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) =
      ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by sorry
