-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotoneStrictPassageDiscountedTailV1
-- name    : Kyprianou.Ch05.monotoneStrictPassageDiscountedTailV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T21:49:30.7308+00:00
-- url     : https://prove2.me/theorems/56c9fb3f-3084-494b-9970-3d6ce467804f
-- title:
--   Discounted occupation above a level equals the exponential clock tail
-- statement:
--   For a monotone path, the strict upper set differs from the open ray above the passage clock by at most its endpoint. That endpoint is Lebesgue-null. Apply the proved Avram exponential-tail integral.
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

theorem Kyprianou.Ch05.monotoneStrictPassageDiscountedTailV1
    (f : NNReal → ℝ) (hm : Monotone f) (x : ℝ) (hx : 0 ≤ x) (hz : f 0 = 0)
    (T : ENNReal)
    (hT : T = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t}))
    (eta : ℝ) (heta : 0 < eta) :
    (∫⁻ t in Ici (0 : ℝ), if x < f t.toNNReal then
        ENNReal.ofReal (Real.exp (-eta*t)) else 0 ∂volume) =
      if T ≠ ⊤ then ENNReal.ofReal (Real.exp (-eta*T.toReal)/eta) else 0 := by
  sorry
