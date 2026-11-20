-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneUntruncatedPositiveGammaValue
-- name    : Kyprianou.Ch01.stableAboveOneUntruncatedPositiveGammaValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:09:39.715303+00:00
-- url     : https://prove2.me/theorems/ce19c821-cd66-4126-bc5c-5bcadd7262b7
-- title:
--   Stable above-one positive untruncated Fourier moment via Gamma integral scaling
-- statement:
--   For 1<alpha<2 and xi>0, the untruncated compensated Fourier integral equals Gamma(-alpha) times the principal complex power of -i xi. Use unit-frequency Gamma integral, positive-halfline scaling by xi^alpha, and the already-Proved positive-frequency phase.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4.

import Mathlib
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneUntruncatedPositiveGammaValue
    (alpha xi : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (hxi : 0 < xi) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
        Complex.I * (((xi * r : ℝ) : ℂ))) /
        (((r ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) =
      (((Real.Gamma (-alpha) : ℝ) : ℂ)) *
        Complex.exp ((alpha : ℂ) *
          Complex.log (-(Complex.I * (xi : ℂ)))) := by sorry
