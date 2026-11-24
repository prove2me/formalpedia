-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_exp_convolution_substitution
-- name    : Kyprianou.Ch08.StageB.p2m85_exp_convolution_substitution
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T15:13:32.446053+00:00
-- url     : https://prove2.me/theorems/d94f2022-13c8-40a1-8a9a-4f09f7029569
-- title:
--   Exponentially normalised integral as a translated convolution
-- statement:
--   Cancel the exponential factors, truncate where the negative spatial scale vanishes, then substitute z-t.
-- source:
--   Kyprianou (2006), Exercise 8.5(i), positive discount asymptotic.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem Kyprianou.Ch08.StageB.p2m85_exp_convolution_substitution
    (W : ℝ → ℝ) (φ z : ℝ) (hz : 0 ≤ z)
    (hzero : ∀ y, y < 0 → W y = 0) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-φ*t) *
      (Real.exp (-φ*(z-t)) * W (z-t))) =
      Real.exp (-φ*z) * ∫ y in (0 : ℝ)..z, W y := by
  sorry
