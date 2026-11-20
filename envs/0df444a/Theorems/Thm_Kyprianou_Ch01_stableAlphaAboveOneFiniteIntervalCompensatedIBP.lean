-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneFiniteIntervalCompensatedIBP
-- name    : Kyprianou.Ch01.stableAlphaAboveOneFiniteIntervalCompensatedIBP
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:02:53.862178+00:00
-- url     : https://prove2.me/theorems/123f343b-953f-4504-9d7f-b7bb5e9d09ba
-- title:
--   Finite positive interval integration by parts for the exact compensated stable Fourier kernel
-- statement:
--   For 1<alpha<2 and 0<a<c, integration by parts on the exact compact interval a..c transforms the compensated complex Fourier kernel (exp(ir)-1-ir) r^(-alpha-1) into the exact boundary term [-(exp(ir)-1-ir)r^(-alpha)/alpha] plus (i/alpha) times the uncompensated kernel (exp(ir)-1)r^(-alpha). This is a genuine finite-interval differential theorem before sending the two endpoints to 0+ and infinity.
-- source:
--   Kyprianou (2006), Chapter 1, compensated stable Fourier exponent; compact-interval integration by parts.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneFiniteIntervalCompensatedIBP
    (alpha a c : ℝ) (ha : 1 < alpha) (hb : alpha < 2)
    (hapos : 0 < a) (hac : a < c) :
    (∫ r in a..c,
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
            Complex.I * (r : ℂ)) *
          (((r ^ (-(alpha + 1) : ℝ) : ℝ)) : ℂ)) =
      (Complex.exp (Complex.I * (a : ℂ)) - 1 -
          Complex.I * (a : ℂ)) *
        (((a ^ (-alpha) : ℝ)) : ℂ) / (alpha : ℂ) -
      (Complex.exp (Complex.I * (c : ℂ)) - 1 -
          Complex.I * (c : ℂ)) *
        (((c ^ (-alpha) : ℝ)) : ℂ) / (alpha : ℂ) +
      (Complex.I / (alpha : ℂ)) *
        (∫ r in a..c,
          (Complex.exp (Complex.I * (r : ℂ)) - 1) *
            (((r ^ (-alpha) : ℝ)) : ℂ)) := by
  sorry
