-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableBelowOneWeightedGammaNegativeFrequency
-- name    : Kyprianou.Ch01.stableBelowOneWeightedGammaNegativeFrequency
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:55:05.18969+00:00
-- url     : https://prove2.me/theorems/62c1bcf9-28f1-41d4-9490-63fe41c2c316
-- title:
--   Negative-frequency below-one stable canonical weighted Gamma factor by coefficient reflection
-- statement:
--   For xi<0 the stable weighted Gamma Fourier expression equals the canonical stable scale multiplied by (1+i beta tan(theta)). Reflect frequency xi to -xi and exchange cpos with cneg in the proven positive-frequency theorem, so beta changes sign while the scale remains unchanged.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, two-sided stable reflection and skewness.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableBelowOneWeightedGammaPositiveFrequency
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableBelowOneWeightedGammaNegativeFrequency
    (alpha cpos cneg xi : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hxi : xi < 0) (hnonzero : 0 < cpos + cneg) :
    let E : ℝ → ℂ := (fun z : ℝ => if z = 0 then (0 : ℂ) else
      Complex.exp ((alpha : ℂ) *
        Complex.log (-(Complex.I * (z : ℂ)))));
    -((Real.Gamma (-alpha) : ℝ) : ℂ) *
      ((cpos : ℂ) * E xi + (cneg : ℂ) * E (-xi)) =
      (((-Real.Gamma (-alpha) * Real.cos (Real.pi * alpha / 2) *
          (cpos + cneg)) * |xi| ^ alpha : ℝ) : ℂ) *
        (1 + Complex.I *
          (((((cpos - cneg) / (cpos + cneg)) *
            Real.tan (Real.pi * alpha / 2) : ℝ) : ℂ))) := by sorry
