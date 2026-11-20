-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneHalfLineProductIBP
-- name    : Kyprianou.Ch01.stableAlphaAboveOneHalfLineProductIBP
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:14:26.755518+00:00
-- url     : https://prove2.me/theorems/9d2c5184-3ed5-4cd1-b941-723abaf5a7d5
-- title:
--   Infinite positive half-line integration by parts for stable compensated Fourier numerator
-- statement:
--   For 1<alpha<2, integrate by parts the exact compensated complex Fourier numerator u(r)=exp(ir)−1−ir against the real power antiderivative v(r)=r^(−alpha)/(−alpha) on the whole positive half-line. Both u(r)*v(r) endpoint limits vanish at 0+ and at infinity by independently Proved bounds. The derivative integrands u*v′ and u′*v are absolutely integrable, using the source α>1 stable kernel and the α−1∈(0,1) Gamma Fourier kernel. The exact result is ∫u v′ = −∫u′ v, with no dropped boundary term.
-- source:
--   Kyprianou (2006), Chapter 1 spectrally negative stable α>1 compensated Fourier integration by parts.

import Mathlib
open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneHalfLineProductIBP
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) *
          (((r ^ (-(alpha + 1)) : ℝ)) : ℂ) ∂volume) =
      -(∫ r in Set.Ioi (0 : ℝ),
        (Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ) ∂volume) := by
  sorry
