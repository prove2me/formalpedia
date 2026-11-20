-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneComplexProductIBP
-- name    : Kyprianou.Ch01.stableAlphaAboveOneComplexProductIBP
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:22:03.96683+00:00
-- url     : https://prove2.me/theorems/44a58a61-8fec-4a7c-bf1e-40308505c40e
-- title:
--   Exact compensated stable Fourier integration-by-parts in the native product-derivative form
-- statement:
--   For 1<alpha<2 and 0<a<c, apply the exact complex-valued finite-interval integration-by-parts theorem to the compensated Fourier numerator u(r)=exp(ir)−1−ir and the real-to-complex power antiderivative v(r)=r^(−alpha)/(−alpha). The derivative u′=i(exp(ir)−1) and v′=r^(−alpha−1) are genuine separately formalised sources. The identity is the exact full boundary-product and residual-integral equation before algebraic simplification.
-- source:
--   Kyprianou (2006), Chapter 1, stable compensated Fourier kernel; positive finite-interval complex integration by parts.

import Mathlib
open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneComplexProductIBP
    (alpha a c : ℝ) (ha : 1 < alpha) (hb : alpha < 2)
    (hapos : 0 < a) (hac : a < c) :
    (∫ r in a..c,
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) *
        (((r ^ (-(alpha + 1)) : ℝ)) : ℂ)) =
      (Complex.exp (Complex.I * (c : ℂ)) - 1 -
        Complex.I * (c : ℂ)) *
        (((c ^ (-alpha) / (-alpha) : ℝ)) : ℂ) -
      (Complex.exp (Complex.I * (a : ℂ)) - 1 -
        Complex.I * (a : ℂ)) *
        (((a ^ (-alpha) / (-alpha) : ℝ)) : ℂ) -
      (∫ r in a..c,
        (Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ)) := by
  sorry
