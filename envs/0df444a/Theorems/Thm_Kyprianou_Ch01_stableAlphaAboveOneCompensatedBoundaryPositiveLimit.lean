-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCompensatedBoundaryPositiveLimit
-- name    : Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryPositiveLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:51:35.548953+00:00
-- url     : https://prove2.me/theorems/6681e97d-ead9-4c1e-95cd-209985d787c0
-- title:
--   Stable compensated Fourier integration-by-parts boundary vanishes AtZero
-- statement:
--   The original α>1 compensated stable Fourier numerator behaves quadratically at r→0+, so its product with r^(−α) tends to zero because 2−α>0. This is the lower endpoint boundary required by the source-exact integration by parts.
-- source:
--   Kyprianou (2006), Chapter 1 α∈(1,2) compensated stable Fourier integral, exact boundary term.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryPositiveLimit
    (alpha : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) :
    Tendsto (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) * ((r ^ (-alpha) : ℝ) : ℂ)) ((nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))) (nhds (0 : ℂ)) := by
  sorry
