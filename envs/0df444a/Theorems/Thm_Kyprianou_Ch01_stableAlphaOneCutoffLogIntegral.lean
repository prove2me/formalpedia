-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffLogIntegral
-- name    : Kyprianou.Ch01.stableAlphaOneCutoffLogIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:44:24.101016+00:00
-- url     : https://prove2.me/theorems/7cb6d2eb-58ba-4132-96a1-b59fe95ebf24
-- title:
--   Logarithmic change-of-cutoff integral for alpha-one stable phase
-- statement:
--   For every z>0, the signed interval integral of 1/r from 1 to z equals log z, including 0<z<1 (negative orientation). This is the exact scale-dependent logarithmic correction when the compensated alpha-one stable kernel cutoff changes from r<1 to r<z.
-- source:
--   Kyprianou (2006), Chapter 1, stable index-one imaginary logarithmic phase.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCutoffLogIntegral
    (z : ℝ) (hz : 0 < z) :
    (∫ r : ℝ in (1 : ℝ)..z, r⁻¹) = Real.log z := by
  sorry
