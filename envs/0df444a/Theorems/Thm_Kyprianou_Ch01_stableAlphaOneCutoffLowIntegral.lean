-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffLowIntegral
-- name    : Kyprianou.Ch01.stableAlphaOneCutoffLowIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:07:54.521216+00:00
-- url     : https://prove2.me/theorems/6a9915fa-0617-4f27-bf2d-f787b9a7d583
-- title:
--   Exact logarithmic integral of the low-frequency stable cutoff difference
-- statement:
--   For 0<z≤1 the full positive-half-line integral (1_(u<z)−1_(u<1))/u equals log z. The integrand is minus 1/u on [z,1); reversing the signed interval integral gives log z. This closes the low-frequency case of the original alpha-one stable phase cutoff.
-- source:
--   Kyprianou (2006), Chapter 1, index-one logarithmic stable phase.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffDifferenceLowFrequency
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffLogIntegral
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCutoffLowIntegral
    (z : ℝ) (hz0 : 0 < z) (hz1 : z ≤ 1) :
    (∫ u in Set.Ioi (0 : ℝ),
      ((if u < z then (1 : ℝ) else 0) -
        (if u < 1 then (1 : ℝ) else 0)) / u ∂volume) =
      Real.log z := by
  sorry
