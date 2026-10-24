-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplex_slice_integral
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplex_slice_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:41:25.418586+00:00
-- url     : https://prove2.me/theorems/3cdcd2bf-1484-4849-90c2-91d647d96233
-- title:
--   Evaluate the simplex slice integral
-- statement:
--   For every natural n, the interval integral of (1−t)^n from 0 to 1 equals 1/(n+1), including n = 0.

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

theorem OAI.PiExponent.DeterminantContradiction.unitSimplex_slice_integral (n : Nat) :
    (∫ t in (0 : Real)..1, (1 - t) ^ n) = 1 / (n + 1 : Real) := by sorry
