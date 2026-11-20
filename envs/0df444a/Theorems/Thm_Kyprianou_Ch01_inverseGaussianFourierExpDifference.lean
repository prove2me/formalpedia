-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierExpDifference
-- name    : Kyprianou.Ch01.inverseGaussianFourierExpDifference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:45:10.68494+00:00
-- url     : https://prove2.me/theorems/ea895657-6b7a-480d-a6a2-5bc1714e6b78
-- title:
--   Inverse-Gaussian oscillatory factor times exponential tilt equals two complex exponential difference
-- statement:
--   For real inverse-Gaussian tilt b, frequency theta, radius r, the original Fourier factor (1-exp(i theta r)) times exp(-b²r/2) equals exp((-b²/2)r)-exp((-b²/2+i theta)r). Pure complex exponential product identity.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.6(ii), inverse Gaussian Fourier tilt identity.

import Mathlib
open MeasureTheory Set Complex Real
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFourierExpDifference (b theta r : ℝ) :
    ((1 : ℂ) - Complex.exp (Complex.I * ((theta * r : ℝ) : ℂ))) *
      ((Real.exp (-(b ^ 2 * r / 2)) : ℝ) : ℂ) =
    Complex.exp (((-(b ^ 2 / 2) : ℝ) : ℂ) * (r : ℂ)) -
      Complex.exp ((((-(b ^ 2 / 2) : ℝ) : ℂ) +
        Complex.I * (theta : ℂ)) * (r : ℂ)) := by sorry
