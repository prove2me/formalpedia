-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneUntruncatedPositiveIntegrable
-- name    : Kyprianou.Ch01.stableAboveOneUntruncatedPositiveIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:52:48.361468+00:00
-- url     : https://prove2.me/theorems/26acc427-43af-47d0-b188-d317c63db7bf
-- title:
--   Above-one positive-frequency original untruncated Fourier kernel integrability by scaling
-- statement:
--   For stable index 1<alpha<2 and xi>0, the untruncated compensated Fourier kernel (exp(i xi r)-1-i xi r)/r^(alpha+1) is complex Bochner integrable on r>0. Transfer the already-Proved unit-frequency integrability by the pinned positive scaling equivalence, using the exact power-product identity.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, stable above-one compensated Fourier exponent.

import Mathlib
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneUntruncatedPositiveIntegrable
    (alpha xi : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (hxi : 0 < xi) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
          Complex.I * (((xi * r : ℝ) : ℂ))) /
          (((r ^ (alpha + 1) : ℝ) : ℂ)))
      (Set.Ioi (0 : ℝ)) := by sorry
