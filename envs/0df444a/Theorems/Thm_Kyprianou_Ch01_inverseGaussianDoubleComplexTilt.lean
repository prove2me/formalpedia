-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianDoubleComplexTilt
-- name    : Kyprianou.Ch01.inverseGaussianDoubleComplexTilt
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:39:11.564183+00:00
-- url     : https://prove2.me/theorems/105eec37-e427-4520-8f7a-636b1056cd2c
-- title:
--   inverseGaussianDoubleComplexTilt
-- statement:
--   Twice the complex half-rate shifted inverse-Gaussian Laplace parameter is exactly b^2-2i theta, with the same principal square-root argument.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.6(ii), exact inverse Gaussian tilted exponent.

import Mathlib
open Complex Real ComplexOrder
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianDoubleComplexTilt
    (b theta : ℝ) :
    (2 : ℂ) *
      (((b ^ 2 / 2 : ℝ) : ℂ) - Complex.I * (theta : ℂ)) =
      ((b ^ 2 : ℝ) : ℂ) - 2 * Complex.I * (theta : ℂ) := by sorry
