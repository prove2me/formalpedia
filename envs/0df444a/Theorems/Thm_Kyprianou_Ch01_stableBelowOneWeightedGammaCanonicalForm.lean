-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableBelowOneWeightedGammaCanonicalForm
-- name    : Kyprianou.Ch01.stableBelowOneWeightedGammaCanonicalForm
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:38:01.329365+00:00
-- url     : https://prove2.me/theorems/b4d8fd27-ef84-4cb6-bfb8-055c5cd34747
-- title:
--   Algebraic conversion of weighted below-one Gamma powers into canonical stable skew normal form
-- statement:
--   For 0<alpha<1 and positive cpos+cneg, the positive/negative-frequency principal Gamma fractional powers convert exactly into stable scale -Gamma(-alpha)cos(pi alpha/2)*(cpos+cneg) and skew ratio times tan times sign. Include xi=0.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, original stable Levy-Khintchine.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableBelowOneWeightedGammaCanonicalForm
    (alpha cpos cneg xi : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hnonzero : 0 < cpos + cneg) :
    let E : ℝ → ℂ := (fun z : ℝ => if z = 0 then (0 : ℂ) else
  Complex.exp ((alpha : ℂ) *
    Complex.log (-(Complex.I * (z : ℂ)))));
    let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
    -((Real.Gamma (-alpha) : ℝ) : ℂ) *
      ((cpos : ℂ) * E xi + (cneg : ℂ) * E (-xi)) =
      (((-Real.Gamma (-alpha) * Real.cos (Real.pi * alpha / 2) *
          (cpos + cneg)) * |xi| ^ alpha : ℝ) : ℂ) *
        (1 - Complex.I *
          (((((cpos - cneg) / (cpos + cneg)) *
            Real.tan (Real.pi * alpha / 2) * sgn : ℝ) : ℂ))) := by sorry
