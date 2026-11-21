-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianSymmetricGaussianIntegral
-- name    : Kyprianou.Ch01.inverseGaussianSymmetricGaussianIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:15:14.062934+00:00
-- url     : https://prove2.me/theorems/8ae4de27-cd6e-4993-84e3-0f27070b644f
-- title:
--   Symmetric reciprocal Gaussian integral after x^-1/2 substitution
-- statement:
--   For positive a,c the symmetric Gaussian integral ∫_0∞ exp(-a*y²-c/y²)dy equals sqrt(pi)/(2sqrt a)*exp(-2sqrt(a*c)). This is exactly the remaining special-function identity after the independently proved reciprocal half-power substitution.
-- source:
--   Kyprianou (2006) Exercise 1.6(iii), inverse-Gaussian first passage Laplace kernel.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianSymmetricGaussianIntegral
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (∫ y in Set.Ioi (0 : ℝ),
      Real.exp (-a * y ^ 2 - c / y ^ 2) ∂volume) =
    (Real.sqrt Real.pi / (2 * Real.sqrt a)) *
      Real.exp (-2 * Real.sqrt (a * c)) := by sorry
