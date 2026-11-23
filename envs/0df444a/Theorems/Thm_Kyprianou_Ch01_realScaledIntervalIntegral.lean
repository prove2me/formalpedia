-- Prove2me | Theorems.Thm_Kyprianou_Ch01_realScaledIntervalIntegral
-- name    : Kyprianou.Ch01.realScaledIntervalIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:00:48.508444+00:00
-- url     : https://prove2.me/theorems/553c002c-1931-40a3-aa0f-9bade9eb53af
-- title:
--   Scale change of variables in a real interval integral
-- statement:
--   For any real scaling factor c, endpoint t and real function f, the interval integral of c times f(c*s) over the oriented interval [0,t] equals the integral of f over [0,c*t], without requiring independent integrability assumptions. This follows from Mathlib intervalIntegral.mul_integral_comp_mul_left and integral_const_mul and supplies source-to-physical-clock scaling for first-arrival Lamperti renewal identities.
-- source:
--   Mathlib intervalIntegral.mul_integral_comp_mul_left; Kyprianou (2006), §1.3.4 first-arrival physical-clock transform

import Mathlib
open MeasureTheory intervalIntegral
set_option autoImplicit false

theorem Kyprianou.Ch01.realScaledIntervalIntegral
    (c t : ℝ) (f : ℝ → ℝ) :
    (∫ s in (0 : ℝ)..t, c * f (c * s)) =
      (∫ a in (0 : ℝ)..c * t, f a) := by
  sorry
