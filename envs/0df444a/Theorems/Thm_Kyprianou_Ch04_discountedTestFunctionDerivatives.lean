-- Prove2me | Theorems.Thm_Kyprianou_Ch04_discountedTestFunctionDerivatives
-- name    : Kyprianou.Ch04.discountedTestFunctionDerivatives
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:05:08.140724+00:00
-- url     : https://prove2.me/theorems/a07e73c0-c40f-4bee-b718-f9c90ef25516
-- title:
--   Directional derivatives of the discounted spatial test function
-- statement:
--   Directional derivatives of the discounted spatial test function.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.SetSemiring
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The two directional derivatives of the discounted spatial test function. -/
theorem Kyprianou.Ch04.discountedTestFunctionDerivatives (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (l s y : ℝ) :
    let g : ℝ × ℝ → ℝ := fun p => Real.exp (-l*p.1)*f p.2
    ContDiff ℝ 1 g ∧
      fderiv ℝ g (s,y) (1,0) = -l * Real.exp (-l*s)*f y ∧
      fderiv ℝ g (s,y) (0,1) = Real.exp (-l*s)*deriv f y := by
  sorry
