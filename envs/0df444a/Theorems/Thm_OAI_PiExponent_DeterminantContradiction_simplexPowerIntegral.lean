-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexPowerIntegral
-- name    : OAI.PiExponent.DeterminantContradiction.simplexPowerIntegral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:27:51.449571+00:00
-- url     : https://prove2.me/theorems/f86aa3ae-bc7e-4be3-9397-8c014b3278eb
-- title:
--   Integral of the simplex scaling power
-- statement:
--   Integrating the ENNReal coercion of (1 - t)^n/n! over t in [0,1] gives the ENNReal coercion of 1/(n+1)!.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- Proof route: establish integrability and nonnegativity on [0,1], evaluate the real interval integral of (1 - t)^n by the antiderivative, then transfer that value through ENNReal.ofReal (or evaluate the corresponding lintegral directly). The factorial identity (n+1)! = (n+1)n! completes the calculation.

theorem OAI.PiExponent.DeterminantContradiction.simplexPowerIntegral (n : Nat) :
    ∫⁻ t in Set.Icc (0 : Real) 1,
      ENNReal.ofReal (((1 - t) ^ n) / (Nat.factorial n : Real))
      ∂MeasureTheory.volume =
    ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by sorry
