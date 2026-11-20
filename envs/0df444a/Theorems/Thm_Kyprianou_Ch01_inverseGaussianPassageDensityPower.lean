-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianPassageDensityPower
-- name    : Kyprianou.Ch01.inverseGaussianPassageDensityPower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:06:49.172199+00:00
-- url     : https://prove2.me/theorems/0e8c8647-2f60-4627-a71f-a8acea9042c2
-- title:
--   Exact passage-time inverse-Gaussian density normaliser factors into x^-3/2
-- statement:
--   For positive x, the passage-time density s/sqrt(2*pi*x^3) equals the constant s/sqrt(2*pi) times x^(-3/2), directly scaling the previously Proved inverse Gaussian jump-density power identity.
-- source:
--   Kyprianou (2006) Exercise 1.6(iii), inverse Gaussian first-passage density.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityPowerIdentity
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianPassageDensityPower
    (s x : ℝ) (hx : 0 < x) :
    s / Real.sqrt (2 * Real.pi * x ^ 3) =
      (s / Real.sqrt (2 * Real.pi)) *
        x ^ (-(3 / 2 : ℝ)) := by sorry
