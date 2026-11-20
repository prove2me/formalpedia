-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneWeightedGammaNegativeFrequency
-- name    : Kyprianou.Ch01.stableAboveOneWeightedGammaNegativeFrequency
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:12:09.218093+00:00
-- url     : https://prove2.me/theorems/af645623-93cb-420f-8b81-f24864f29a24
-- title:
--   Negative-frequency above-one weighted Gamma stable skew factor
-- statement:
--   Reflection xi to -xi and swapping cpos,cneg in the positive frequency above-one Gamma phase changes the canonical skewness sign while preserving stable scale for 1<alpha<2.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4 stable exponent.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneWeightedGammaNegativeFrequency
    (alpha cpos cneg xi : ℝ)
    (ha1 : 1 < alpha) (ha2 : alpha < 2)
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
