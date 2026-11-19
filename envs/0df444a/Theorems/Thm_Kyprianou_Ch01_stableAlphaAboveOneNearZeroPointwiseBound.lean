-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneNearZeroPointwiseBound
-- name    : Kyprianou.Ch01.stableAlphaAboveOneNearZeroPointwiseBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:19:14.027513+00:00
-- url     : https://prove2.me/theorems/19d3a944-0c6b-42ba-87bb-763647c069d2
-- title:
--   Quadratic near-zero stable Fourier kernel bound
-- statement:
--   At all r∈(0,1], the complex stable compensated numerator exp(i*r)-1-i*r has quadratic Taylor remainder bounded by r², so the original kernel norm is ≤r^(1-alpha) after dividing by r^(alpha+1).
-- source:
--   Kyprianou 2006 Chapter 1, alpha>1 stable compensated characteristic integral, exact pointwise component of envelope bound.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneNearZeroPointwiseBound
    (alpha r : ℝ) (hr : 0 < r) (hsmall : r ≤ 1) :
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) /
          (((r ^ (alpha + 1) : ℝ)) : ℂ)‖ ≤ r ^ (1 - alpha) := by
  sorry
