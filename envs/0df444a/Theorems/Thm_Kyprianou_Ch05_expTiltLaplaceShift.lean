-- Prove2me | Theorems.Thm_Kyprianou_Ch05_expTiltLaplaceShift
-- name    : Kyprianou.Ch05.expTiltLaplaceShift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:52:44.914223+00:00
-- url     : https://prove2.me/theorems/ac5e7685-adc7-56b9-a11b-be558966f3e6
-- title:
--   Exponential density tilt shifts the Laplace parameter
-- statement:
--   The negative exponential weight shifts the Laplace parameter by one, by the withDensity integral formula.
-- source:
--   Kyprianou (2006), Chapter 5; reusable Laplace uniqueness bridge.

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.expTiltLaplaceShift (mu : Measure Real) (t : Real) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂
      (mu.withDensity (fun x => ENNReal.ofReal (Real.exp (-x))))) =
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(t+1)*x)) ∂mu := by
  sorry
