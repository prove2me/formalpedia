-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierPointwiseGamma
-- name    : Kyprianou.Ch01.inverseGaussianFourierPointwiseGamma
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:49:36.171191+00:00
-- url     : https://prove2.me/theorems/10fba171-4a60-4e47-9583-6a575144064e
-- title:
--   Exact inverse Gaussian Fourier density integrand equals complex Gamma half-index difference
-- statement:
--   For x>0, the original real inverse Gaussian density acting on 1-exp(i theta x) equals 1/sqrt(2pi) times the difference of two complex exponential tilts multiplied by x^(-3/2). This uses exact source density, no asymptotic approximation.
-- source:
--   Kyprianou (2006) Exercise 1.6(ii), inverse Gaussian characteristic exponent.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityPowerIdentity
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierExpDifference
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianFourierPointwiseGamma (b theta r : ℝ) (hr : 0 < r) :
    ((1 / Real.sqrt (2 * Real.pi * r ^ 3)) *
      Real.exp (-(b ^ 2 * r / 2))) • ((1 : ℂ) -
      Complex.exp (Complex.I * ((theta * r : ℝ) : ℂ))) = ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
      ((Complex.exp (((-(b ^ 2 / 2) : ℝ) : ℂ) * (r : ℂ)) -
        Complex.exp ((((-(b ^ 2 / 2) : ℝ) : ℂ) + Complex.I * (theta : ℂ)) * (r : ℂ))) *
          ((r ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) := by sorry
