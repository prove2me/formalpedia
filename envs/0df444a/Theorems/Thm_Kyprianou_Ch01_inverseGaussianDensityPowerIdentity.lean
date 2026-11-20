-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityPowerIdentity
-- name    : Kyprianou.Ch01.inverseGaussianDensityPowerIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:44:38.555274+00:00
-- url     : https://prove2.me/theorems/0f030b49-08e0-4bd4-983d-aa20a762b147
-- title:
--   Exact inverse-Gaussian x cubed square-root density equals positive x power minus three halves
-- statement:
--   For every strictly positive radius r, 1/sqrt(2 pi r³)=(1/sqrt(2pi))*r^(-3/2). This is exactly the inverse-Gaussian Lévy density factorisation needed to apply the half-index Gamma integral.
-- source:
--   Kyprianou (2006) Chapter 1 Example 1.6(ii), inverse Gaussian Lévy density.

import Mathlib
open MeasureTheory Set Complex Real
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianDensityPowerIdentity (r : ℝ) (hr : 0 < r) :
    (1 / Real.sqrt (2 * Real.pi * r ^ 3)) =
      (1 / Real.sqrt (2 * Real.pi)) * r ^ (-(3 / 2 : ℝ)) := by sorry
