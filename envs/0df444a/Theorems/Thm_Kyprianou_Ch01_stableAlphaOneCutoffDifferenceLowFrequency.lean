-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffDifferenceLowFrequency
-- name    : Kyprianou.Ch01.stableAlphaOneCutoffDifferenceLowFrequency
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:55:44.506886+00:00
-- url     : https://prove2.me/theorems/dc573f1a-8a17-4cf2-9c16-7ee13964d9a9
-- title:
--   Low-frequency compensation cutoff difference supported on [z,1) with negative sign
-- statement:
--   For 0<z≤1, the difference between the compensation cutoffs 1_(u<z) and 1_(u<1), divided by u, is the negative inverse function on z≤u<1 and zero elsewhere. This is the low-frequency counterpart of the logarithmic alpha-one Lévy phase cutoff identity, including the reversed interval orientation.
-- source:
--   Kyprianou (2006), Chapter 1, alpha-one stable imaginary logarithmic phase.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCutoffDifferenceLowFrequency
    (z u : ℝ) (hz0 : 0 < z) (hz1 : z ≤ 1) :
    ((if u < z then (1 : ℝ) else 0) -
      (if u < 1 then (1 : ℝ) else 0)) / u =
        -((Set.Ico z (1 : ℝ)).indicator (fun x : ℝ => x⁻¹) u) := by
  sorry
