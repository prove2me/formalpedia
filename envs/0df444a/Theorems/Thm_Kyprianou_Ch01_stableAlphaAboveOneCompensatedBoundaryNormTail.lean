-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCompensatedBoundaryNormTail
-- name    : Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryNormTail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:32:14.399532+00:00
-- url     : https://prove2.me/theorems/ea4d8725-84ff-4c14-8619-4996fba73db7
-- title:
--   Stable alpha above one compensated Fourier boundary norm Tail estimate
-- statement:
--   For alpha∈(1,2) and r>1, the norm of the unchanged compensated complex Fourier boundary term (exp(ir)-1-ir)*r^-alpha is at most 2*r^(1-alpha), by the global imaginary exponential difference estimate and triangle inequality.
-- source:
--   Kyprianou (2006) Chapter 1 α∈(1,2) stable compensated Fourier integral, pointwise boundary estimate.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryNormTail
    (alpha r : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) (hr : 1 < r) :
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) * (((r ^ (-alpha)) : ℝ) : ℂ)‖ ≤
      2 * r ^ (1 - alpha) := by
  sorry
