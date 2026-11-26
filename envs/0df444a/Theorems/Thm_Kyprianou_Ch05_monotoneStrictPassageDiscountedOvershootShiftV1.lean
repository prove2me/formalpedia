-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotoneStrictPassageDiscountedOvershootShiftV1
-- name    : Kyprianou.Ch05.monotoneStrictPassageDiscountedOvershootShiftV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T22:06:39.484326+00:00
-- url     : https://prove2.me/theorems/7814204d-19ea-5bb4-8f64-817b798cf033
-- title:
--   Pathwise weighted occupation factors at the strict passage clock
-- statement:
--   Restrict weighted occupation to the open ray after passage, translate that ray to zero, split the exponential into its stopped payoff and fresh-increment factors, and pull the constant payoff outside the integral.
-- source:
--   Kyprianou (2006), Chapter 5, Exercise 5.8.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Topology Kyprianou.Ch05
open scoped Classical Topology

theorem Kyprianou.Ch05.monotoneStrictPassageDiscountedOvershootShiftV1
    (f : NNReal → ℝ) (hm : Monotone f) (x : ℝ) (hx : 0 ≤ x) (hz : f 0 = 0)
    (T : ENNReal)
    (hT : T = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t}))
    (eta beta : ℝ) :
    (∫⁻ t in Ici (0 : ℝ), if x < f t.toNNReal then
      ENNReal.ofReal (Real.exp (-eta*t-beta*(f t.toNNReal-x))) else 0 ∂volume) =
    if T ≠ ⊤ then
      ENNReal.ofReal (Real.exp (-eta*T.toReal-beta*(f T.toNNReal-x))) *
        (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal
          (Real.exp (-eta*s-beta*(f (T.toNNReal+s.toNNReal)-f T.toNNReal))) ∂volume)
    else 0 := by
  sorry
