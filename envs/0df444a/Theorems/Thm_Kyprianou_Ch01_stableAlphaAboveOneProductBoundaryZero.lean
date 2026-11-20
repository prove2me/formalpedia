-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneProductBoundaryZero
-- name    : Kyprianou.Ch01.stableAlphaAboveOneProductBoundaryZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:18:18.874102+00:00
-- url     : https://prove2.me/theorems/c4560b8f-440d-44f5-9e31-b593e74a237a
-- title:
--   Zero endpoint limits of the exact compensated Fourier numerator times negative-power antiderivative
-- statement:
--   The exact boundary product is the compensated source numerator times r^(−alpha) scaled by the fixed nonzero constant −1/alpha. Its zero limits at 0+ and at infinity follow separately from two already Proved α>1 endpoint-limit theorems.
-- source:
--   Kyprianou (2006), Chapter 1 compensated α>1 Fourier integral, source-exact half-line integration by parts.

import Mathlib
open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneProductBoundaryZero
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    Tendsto
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℂ)) ∧
    Tendsto
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      Filter.atTop (nhds (0 : ℂ)) := by sorry
