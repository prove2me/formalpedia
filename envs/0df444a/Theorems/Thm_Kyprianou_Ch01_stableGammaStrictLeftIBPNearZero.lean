-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftIBPNearZero
-- name    : Kyprianou.Ch01.stableGammaStrictLeftIBPNearZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:24:20.339074+00:00
-- url     : https://prove2.me/theorems/ba913ceb-a9d3-45a7-bdc6-8d0ce834c415
-- title:
--   Stable Gamma complex boundary product at zero
-- statement:
--   Stable Gamma complex boundary product at zero, retaining the exact primitive (exp(wr)-1)r^(−alpha)/(−alpha), source alpha ∈ (0,1), strict negative real part Re(w)<0. This is an independent half-line integration-by-parts endpoint requirement; near zero the product is O(r^(1-alpha)), and at infinity the negative power tends to zero while exp(wr) decays.
-- source:
--   Kyprianou (2006), Chapter 1, stable complex Gamma deficit integral, integration-by-parts boundary.

import Mathlib
open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftIBPNearZero
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    Tendsto
      (fun r : ℝ => (Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℂ)) := by sorry
