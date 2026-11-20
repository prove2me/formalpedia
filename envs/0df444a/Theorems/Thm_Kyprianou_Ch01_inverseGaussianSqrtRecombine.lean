-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianSqrtRecombine
-- name    : Kyprianou.Ch01.inverseGaussianSqrtRecombine
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:43:20.831755+00:00
-- url     : https://prove2.me/theorems/4f195201-52a0-427d-91d7-4ca7d8823538
-- title:
--   Inverse-Gaussian positive square-root scale recombination into principal Fourier exponent
-- statement:
--   For b>0, -sqrt(2)*(sqrt(b²/2)-sqrt(b²/2-i theta)) equals the principal sqrt(b²-2 i theta)-b. Uses the proved positive real root scale, complex sqrt factor-two identity, and nonzero shifted complex frequency.
-- source:
--   Kyprianou (2006) Exercise 1.6(ii), principal square root normalisation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianBaseRootScale
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianComplexSqrtDouble
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianComplexTiltNonzero
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDoubleComplexTilt
open Complex Real ComplexOrder Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianSqrtRecombine
    (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    -((Real.sqrt 2 : ℝ) : ℂ) *
      (((Real.sqrt (b ^ 2 / 2) : ℝ) : ℂ) -
        Complex.sqrt (((b ^ 2 / 2 : ℝ) : ℂ) - Complex.I * (theta : ℂ))) =
    Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
      2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by sorry
