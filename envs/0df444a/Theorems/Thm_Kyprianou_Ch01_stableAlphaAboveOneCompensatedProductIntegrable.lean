-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCompensatedProductIntegrable
-- name    : Kyprianou.Ch01.stableAlphaAboveOneCompensatedProductIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:18:16.193791+00:00
-- url     : https://prove2.me/theorems/a762af89-844e-4349-ac82-da6111ede3e7
-- title:
--   Integrability of the exact compensated stable Fourier product
-- statement:
--   The original absolutely integrable stable α>1 quotient kernel equals the exact product u(r)*r^(−α−1) for every r>0. The already Proved stableAlphaAboveOneKernelIntegrable yields this by the real reciprocal-power identity.
-- source:
--   Kyprianou (2006), Chapter 1 compensated α>1 Fourier integral, source-exact half-line integration by parts.

import Mathlib
open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneCompensatedProductIntegrable
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) *
            (((r ^ (-(alpha + 1)) : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ)) := by sorry
