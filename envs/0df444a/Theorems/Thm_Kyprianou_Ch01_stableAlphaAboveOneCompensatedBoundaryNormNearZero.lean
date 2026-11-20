-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCompensatedBoundaryNormNearZero
-- name    : Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryNormNearZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:32:11.563305+00:00
-- url     : https://prove2.me/theorems/a09c323a-5e33-4a47-a187-3253947e4520
-- title:
--   Stable alpha above one compensated Fourier boundary norm NearZero estimate
-- statement:
--   For alpha∈(1,2) and 0<r≤1, the norm of the unchanged compensated complex Fourier boundary term (exp(ir)-1-ir)*r^-alpha is at most r^(2-alpha), by the quadratic complex exponential Taylor remainder.
-- source:
--   Kyprianou (2006) Chapter 1 α∈(1,2) stable compensated Fourier integral, pointwise boundary estimate.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryNormNearZero
    (alpha r : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) * (((r ^ (-alpha)) : ℝ) : ℂ)‖ ≤
      r ^ (2 - alpha) := by
  sorry
