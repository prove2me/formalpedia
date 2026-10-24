-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_inverse_factorial_succ
-- name    : OAI.PiExponent.DeterminantContradiction.inverse_factorial_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:14:31.482272+00:00
-- url     : https://prove2.me/theorems/b984f132-8ef9-47a2-b04b-a3c2a4017848
-- title:
--   Inverse factorial successor identity in ENNReal
-- statement:
--   The inverse-factorial volume expression in dimension `n + 1` is the dimension-`n` expression multiplied by `1/(n+1)`. Prove this independently from the successor formula for factorials, positivity of the factors, and multiplication of nonnegative real values under `ENNReal.ofReal`; it isolates the arithmetic and coercion work needed by the parent.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.inverse_factorial_succ (n : Nat) :
    ENNReal.ofReal (1 / ((Nat.factorial (n + 1) : Nat) : Real)) =
      ENNReal.ofReal (1 / ((Nat.factorial n : Nat) : Real)) *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by sorry
