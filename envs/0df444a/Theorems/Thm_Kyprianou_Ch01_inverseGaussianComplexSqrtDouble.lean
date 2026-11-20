-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianComplexSqrtDouble
-- name    : Kyprianou.Ch01.inverseGaussianComplexSqrtDouble
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:40:45.762185+00:00
-- url     : https://prove2.me/theorems/f394bb0c-0c13-4742-a9ef-1162f95e6277
-- title:
--   Complex principal square root scales by the positive real square root of two
-- statement:
--   For any nonzero complex z, the principal square root of 2z equals sqrt(2) times the principal square root of z; the multiplier 2 is strictly positive real, so the principal branch is preserved.
-- source:
--   Mathlib Complex.sqrt_eq_exp, log_ofReal_mul; Kyprianou Chapter 1 inverse Gaussian exponent square-root normalisation.

import Mathlib
open Complex Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianComplexSqrtDouble (z : ℂ) (hz : z ≠ 0) :
    Complex.sqrt ((2 : ℂ) * z) =
      ((Real.sqrt 2 : ℝ) : ℂ) * Complex.sqrt z := by sorry
