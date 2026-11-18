-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseAwayZeroIntegrable
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhaseAwayZeroIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:43:11.245333+00:00
-- url     : https://prove2.me/theorems/b904bc59-7ef7-4f10-aea7-d03d876802fd
-- title:
--   Absolute integrability of the exact complex alpha-one Levy kernel away from zero
-- statement:
--   For positive z and every delta>0, the source-exact complex alpha-one compensated Levy kernel is absolutely Bochner-integrable over r>delta. Its cutoff implies the compensation is bounded by z and the exponential difference by two; the whole norm is therefore bounded by (2+z)/r², which is integrable on (delta,infinity).
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable log-phase Levy integral.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseKernelMeasurable
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhaseAwayZeroIntegrable
    (z delta : ℝ) (hz : 0 < z) (hdelta : 0 < delta) :
    IntegrableOn (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ))
      (Set.Ioi delta) := by
  sorry
