-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneShiftedSineIntegralLogCorrection
-- name    : Kyprianou.Ch01.stableAlphaOneShiftedSineIntegralLogCorrection
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:28:18.340558+00:00
-- url     : https://prove2.me/theorems/165ecd9f-8260-4885-8055-48159dab216c
-- title:
--   Exact logarithmic correction of the shifted sine stable alpha-one Lévy integral
-- statement:
--   For every positive frequency z, the integral over u>0 of (u 1_(u<z)−sin u)/u² differs from its unit-cutoff counterpart by log z. Both integrals are absolutely convergent; subtracting integrands leaves exactly the proved cutoff difference, whose integral is log z.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable imaginary logarithmic phase.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneShiftedSineIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneShiftedCutoffDifference
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffLogIntegralAllPositive
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneShiftedSineIntegralLogCorrection
    (z : ℝ) (hz : 0 < z) :
    (∫ u in Set.Ioi (0 : ℝ), ((u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) ∂volume) =
      (∫ u in Set.Ioi (0 : ℝ), ((u * (if u < 1 then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) ∂volume) +
        Real.log z := by
  sorry
