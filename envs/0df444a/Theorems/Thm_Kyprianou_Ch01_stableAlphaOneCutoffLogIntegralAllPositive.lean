-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffLogIntegralAllPositive
-- name    : Kyprianou.Ch01.stableAlphaOneCutoffLogIntegralAllPositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:19:30.672306+00:00
-- url     : https://prove2.me/theorems/c39d3ce5-3a5d-4893-b91b-bca8d44dfaee
-- title:
--   Logarithmic alpha-one compensation cutoff integral for all positive frequencies
-- statement:
--   For every positive frequency z, the positive-half-line Lebesgue integral of (1_(u<z)−1_(u<1))/u equals log z. This joins the high- and low-frequency cases and is the precise logarithmic phase correction from the source cutoff in Kyprianou Chapter 1.
-- source:
--   Kyprianou (2006), Chapter 1, index-one Lévy stable logarithmic phase.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffHighIntegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffLowIntegral
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCutoffLogIntegralAllPositive
    (z : ℝ) (hz : 0 < z) :
    (∫ u in Set.Ioi (0 : ℝ),
      ((if u < z then (1 : ℝ) else 0) -
        (if u < 1 then (1 : ℝ) else 0)) / u ∂volume) =
      Real.log z := by
  sorry
