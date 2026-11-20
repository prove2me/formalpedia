-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianComplexTiltNonzero
-- name    : Kyprianou.Ch01.inverseGaussianComplexTiltNonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:39:10.928563+00:00
-- url     : https://prove2.me/theorems/dbf5dcc4-b929-410a-809c-8d5ae65b5440
-- title:
--   inverseGaussianComplexTiltNonzero
-- statement:
--   The positive real component b^2/2 of the inverse-Gaussian shifted complex Laplace parameter guarantees nonzero for every Fourier frequency.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.6(ii), exact inverse Gaussian tilted exponent.

import Mathlib
open Complex Real ComplexOrder
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianComplexTiltNonzero
    (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    (((b ^ 2 / 2 : ℝ) : ℂ) - Complex.I * (theta : ℂ)) ≠ 0 := by sorry
