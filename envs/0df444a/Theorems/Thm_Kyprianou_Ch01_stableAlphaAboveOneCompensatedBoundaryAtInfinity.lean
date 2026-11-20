-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCompensatedBoundaryAtInfinity
-- name    : Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryAtInfinity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:31:28.942552+00:00
-- url     : https://prove2.me/theorems/d17f5c17-b3ee-4d4f-8d2e-02684121508a
-- title:
--   Stable compensated Fourier integration-by-parts boundary vanishes AtInfinity
-- statement:
--   The original α>1 compensated stable Fourier numerator grows at most linearly as r→+∞, so its product with r^(−α) tends to zero because 1−α<0. This is the upper endpoint boundary required by integration by parts.
-- source:
--   Kyprianou (2006), Chapter 1 α∈(1,2) compensated stable Fourier integral, exact boundary term.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryAtInfinity
    (alpha : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) :
    Tendsto (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) * ((r ^ (-alpha) : ℝ) : ℂ)) Filter.atTop (nhds (0 : ℂ)) := by
  sorry
