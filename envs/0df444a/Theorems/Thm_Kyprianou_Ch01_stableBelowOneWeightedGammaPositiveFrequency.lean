-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableBelowOneWeightedGammaPositiveFrequency
-- name    : Kyprianou.Ch01.stableBelowOneWeightedGammaPositiveFrequency
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:51:05.680514+00:00
-- url     : https://prove2.me/theorems/6885700c-76f1-481c-9188-0a89031d4a4a
-- title:
--   Positive-frequency below-one weighted Gamma stable skewness identity
-- statement:
--   For 0<alpha<1 and positive xi, combine the proved positive/negative principal Gamma phases with the exact weighted complex exponential skewness lemma to obtain canonical stable scale -Gamma(-alpha)cos(pi alpha/2)(cpos+cneg) and beta tan(theta).
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, original stable law exponent.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableGammaPositiveFrequencyPhase
import Theorems.Thm_Kyprianou_Ch01_stableGammaNegativeFrequencyPhase
import Theorems.Thm_Kyprianou_Ch01_stableWeightedExponentialPhase
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableBelowOneWeightedGammaPositiveFrequency
    (alpha cpos cneg xi : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
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
