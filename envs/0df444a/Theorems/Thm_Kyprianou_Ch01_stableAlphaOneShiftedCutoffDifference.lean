-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneShiftedCutoffDifference
-- name    : Kyprianou.Ch01.stableAlphaOneShiftedCutoffDifference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:54:30.492085+00:00
-- url     : https://prove2.me/theorems/7e34c013-20b7-4a2d-83d5-96bc7707b2d9
-- title:
--   Exact pointwise difference of shifted compensated sine kernels
-- statement:
--   At every real u, subtracting the unit-cutoff compensated sine kernel from the cutoff-z version cancels the sine terms and leaves (1_{u<z}−1_{u<1})/u. This holds at u=0 by total division and explicitly isolates the logarithmic 1/u contribution of the alpha-one stable Lévy phase.
-- source:
--   Kyprianou (2006), Chapter 1, alpha-one stable imaginary logarithmic phase.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneShiftedCutoffDifference
    (z u : ℝ) :
    ((u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) -
      ((u * (if u < 1 then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) =
        ((if u < z then (1 : ℝ) else 0) -
          (if u < 1 then (1 : ℝ) else 0)) / u := by
  sorry
