-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneWeightedGammaPositiveFrequency
-- name    : Kyprianou.Ch01.stableAboveOneWeightedGammaPositiveFrequency
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:06:07.578248+00:00
-- url     : https://prove2.me/theorems/55fd7a5f-b1ac-4707-99f3-92bc49a781a4
-- title:
--   Positive Fourier-frequency above-one weighted Gamma stable canonical factor
-- statement:
--   For 1<alpha<2 and positive xi, combine the proved principal complex power phases and weighted complex skew algebra. The cosine of pi alpha/2 is negative and nonzero. The resulting formula has canonical stable scale and tan skew factor, with the original cpos and cneg coefficients.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4 stable Levy exponent.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableGammaPositiveFrequencyPhase
import Theorems.Thm_Kyprianou_Ch01_stableGammaNegativeFrequencyPhase
import Theorems.Thm_Kyprianou_Ch01_stableWeightedExponentialPhase
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneWeightedGammaPositiveFrequency
    (alpha cpos cneg xi : ℝ)
    (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (hxi : 0 < xi) (hnonzero : 0 < cpos + cneg) :
    let E : ℝ → ℂ := (fun z : ℝ => if z = 0 then (0 : ℂ) else
      Complex.exp ((alpha : ℂ) *
        Complex.log (-(Complex.I * (z : ℂ)))));
    -((Real.Gamma (-alpha) : ℝ) : ℂ) *
      ((cpos : ℂ) * E xi + (cneg : ℂ) * E (-xi)) =
      (((-Real.Gamma (-alpha) * Real.cos (Real.pi * alpha / 2) *
          (cpos + cneg)) * |xi| ^ alpha : ℝ) : ℂ) *
        (1 - Complex.I *
          (((((cpos - cneg) / (cpos + cneg)) *
            Real.tan (Real.pi * alpha / 2) : ℝ) : ℂ))) := by sorry
