-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplex_factorial_step_repair4
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplex_factorial_step_repair4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:47:04.766072+00:00
-- url     : https://prove2.me/theorems/0d467436-cf15-47fc-a6e7-756f892dc459
-- title:
--   Convert the slice factor to a factorial
-- statement:
--   For every natural n, the product of the reciprocal n-factorial and reciprocal n+1 is the reciprocal successor factorial, including at n = 0.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic

theorem OAI.PiExponent.DeterminantContradiction.unitSimplex_factorial_step_repair4 (n : Nat) :
    (1 / (Nat.factorial n : Real)) * (1 / (n + 1 : Real)) =
      1 / (Nat.factorial (n + 1) : Real) := by sorry
