-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneNegativePowerAntiderivative
-- name    : Kyprianou.Ch01.stableAlphaAboveOneNegativePowerAntiderivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:10:55.914609+00:00
-- url     : https://prove2.me/theorems/a277f893-73da-41b0-8334-5764cc7cf0be
-- title:
--   Power antiderivative for positive stable compensation r to the negative alpha minus one
-- statement:
--   For the exact α∈(1,2) stable Fourier kernel and positive r, the real function r↦r^(−alpha)/(−alpha) is differentiable with derivative r^(−alpha−1). The formula follows from pinned Mathlib Real.hasDerivAt_rpow_const, nonzero alpha and elementary exponent algebra. This is the v′ factor for the finite-interval source-exact integration by parts.
-- source:
--   Kyprianou (2006) Chapter 1 stable index 1<alpha<2, integration-by-parts power antiderivative.

import Mathlib
open Real Complex MeasureTheory Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneNegativePowerAntiderivative
    (alpha r : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => t ^ (-alpha) / (-alpha))
      (r ^ (-(alpha + 1))) r := by
  sorry
