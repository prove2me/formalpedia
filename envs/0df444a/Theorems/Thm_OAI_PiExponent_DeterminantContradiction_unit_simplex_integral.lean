-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unit_simplex_integral
-- name    : OAI.PiExponent.DeterminantContradiction.unit_simplex_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:18:40.115884+00:00
-- url     : https://prove2.me/theorems/3b0a1d4d-202c-4e23-b447-d02e7cf8a4aa
-- title:
--   Integral of the simplex slice factor
-- statement:
--   Evaluate the one-variable integral of (1 − t)^n on [0,1] as 1/(n+1), by an antiderivative or induction and the fundamental theorem of calculus. This also holds at n = 0.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem OAI.PiExponent.DeterminantContradiction.unit_simplex_integral (n : Nat) :
    (∫ t in (0 : Real)..1, (1 - t) ^ n) = 1 / ((n + 1 : Nat) : Real) := by sorry
