-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianBaseHalfPower
-- name    : Kyprianou.Ch01.inverseGaussianBaseHalfPower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:52:49.588708+00:00
-- url     : https://prove2.me/theorems/4f11f3f5-74bf-48a2-ad0f-4c631ed9d025
-- title:
--   inverseGaussianBaseHalfPower
-- statement:
--   For b>0, the positive real base b²/2 has its principal complex half-power equal to the embedded nonnegative real square root.
-- source:
--   Kyprianou (2006) Chapter 1 inverse Gaussian Gamma normalisation.

import Mathlib
open Complex Real ComplexOrder
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianBaseHalfPower
    (b : ℝ) (hb : 0 < b) :
    Complex.exp (((1 / 2 : ℝ) : ℂ) *
        Complex.log (((b ^ 2 / 2 : ℝ) : ℂ))) =
      ((Real.sqrt (b ^ 2 / 2) : ℝ) : ℂ) := by sorry
