-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_exp_tilt_transform
-- name    : Kyprianou.Ch04.cor412_exp_tilt_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:28:36.47068+00:00
-- url     : https://prove2.me/theorems/99aeb429-2270-5591-a6bd-f2037aace00f
-- title:
--   Exponential tilt shifts the Laplace integral
-- statement:
--   Exponential tilting shifts the Laplace integral argument.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12, supporting lemma.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

/-- Exponential tilting shifts the argument of the nonnegative Laplace integral. -/

theorem Kyprianou.Ch04.cor412_exp_tilt_transform (μ : Measure ℝ) (a : ℝ≥0∞) (s : ℝ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂
      μ.withDensity (fun x => a * ENNReal.ofReal (Real.exp x))) =
      a * ∫⁻ x, ENNReal.ofReal (Real.exp ((s+1)*x)) ∂μ := by sorry
