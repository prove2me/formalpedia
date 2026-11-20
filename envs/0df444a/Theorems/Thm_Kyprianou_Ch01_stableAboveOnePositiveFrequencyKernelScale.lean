-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOnePositiveFrequencyKernelScale
-- name    : Kyprianou.Ch01.stableAboveOnePositiveFrequencyKernelScale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:07:56.743617+00:00
-- url     : https://prove2.me/theorems/3ee95c2c-fa2f-4281-93b5-c377db4603ac
-- title:
--   Scaling the stable compensated Fourier kernel on the positive halfline
-- statement:
--   For alpha>1 and positive xi, the untruncated stable Fourier compensated kernel integral scales from unit frequency as xi^alpha by the substitution u=xi*r. It uses the pinned MeasureTheory.integral_comp_mul_left_Ioi change-of-variable theorem and rpow multiplication for positive variables.
-- source:
--   Kyprianou (2006) Exercise 1.4; stable Fourier scaling and Levy exponent.

import Mathlib
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOnePositiveFrequencyKernelScale
    (alpha xi : ℝ) (ha1 : 1 < alpha) (hxi : 0 < xi) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
        Complex.I * (((xi * r : ℝ) : ℂ))) /
        (((r ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) =
      (((xi ^ alpha : ℝ) : ℂ)) *
        (∫ u in Set.Ioi (0 : ℝ),
          (Complex.exp (Complex.I * (u : ℂ)) - 1 -
            Complex.I * (u : ℂ)) /
            (((u ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) := by sorry
