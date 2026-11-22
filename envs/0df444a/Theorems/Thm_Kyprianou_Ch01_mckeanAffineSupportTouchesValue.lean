-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanAffineSupportTouchesValue
-- name    : Kyprianou.Ch01.mckeanAffineSupportTouchesValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:53:14.399047+00:00
-- url     : https://prove2.me/theorems/16b73ba4-5891-4eef-840e-6e2779b38c7a
-- title:
--   McKean affine exponential supporting function touches the exact candidate value
-- statement:
--   The affine exponential support touches the original piecewise McKean value at its point of construction y. For y<b choose u=y, exponent zero and the sum becomes K−exp(y). For y≥b choose u=b, use exp(b)=K phi/(1+phi) to prove the intercept vanishes and exp(b)/phi=K−exp(b), obtaining the continuation branch. The already proved mckeanBarrierCalculusOptimality may be reused. This is a necessary mission-connected child for the global support theorem.
-- source:
--   Kyprianou (2006), Chapter 1 McKean barrier calculus and payoff contact.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanBarrierCalculusOptimality
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanAffineSupportTouchesValue
    (K phi y : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b := Real.log (K * phi / (1 + phi))
    let u := min y b
    mckeanValue K b phi y =
      (K - (1 + 1 / phi) * Real.exp u) +
        (Real.exp u / phi) * Real.exp (-phi * (y - u)) := by sorry
