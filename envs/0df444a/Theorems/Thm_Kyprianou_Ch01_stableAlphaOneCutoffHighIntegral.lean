-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffHighIntegral
-- name    : Kyprianou.Ch01.stableAlphaOneCutoffHighIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:58:12.833784+00:00
-- url     : https://prove2.me/theorems/702e8be5-eac5-4345-b123-74e61d914e12
-- title:
--   Exact logarithmic integral of the high-frequency stable cutoff difference
-- statement:
--   For z≥1, the positive-half-line integral of (1_(u<z)−1_(u<1))/u equals log z. Use the source-exact cutoff support identity on [1,z), the fact this set lies in u>0, and Mathlib interval integral of 1/u. The result rigorously identifies the positive-frequency logarithmic correction.
-- source:
--   Kyprianou (2006), Chapter 1, index-one logarithmic stable phase.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffDifferenceHighFrequency
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffLogIntegral
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCutoffHighIntegral
    (z : ℝ) (hz : 1 ≤ z) :
    (∫ u in Set.Ioi (0 : ℝ),
      ((if u < z then (1 : ℝ) else 0) -
        (if u < 1 then (1 : ℝ) else 0)) / u ∂volume) =
      Real.log z := by
  sorry
