-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneTailPointwiseBound
-- name    : Kyprianou.Ch01.stableAlphaAboveOneTailPointwiseBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:19:12.28171+00:00
-- url     : https://prove2.me/theorems/cc2442ab-6ded-4b22-abc2-f11dd1fe6126
-- title:
--   Linear far-tail stable Fourier kernel bound
-- statement:
--   For all r>1, the global imaginary-exponential difference bound and triangle inequality give ||exp(i*r)-1-i*r||≤2r, hence the original compensated stable kernel norm is ≤2*r^(-alpha).
-- source:
--   Kyprianou 2006 Chapter 1, alpha>1 stable compensated characteristic integral, exact pointwise component of envelope bound.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneTailPointwiseBound
    (alpha r : ℝ) (hr : 1 < r) :
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) /
          (((r ^ (alpha + 1) : ℝ)) : ℂ)‖ ≤ 2 * r ^ (-alpha) := by
  sorry
