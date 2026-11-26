-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotoneStrictPassageWeightedOccupationV1
-- name    : Kyprianou.Ch05.monotoneStrictPassageWeightedOccupationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:02:35.12474+00:00
-- url     : https://prove2.me/theorems/93063aec-3015-5bcf-91ec-e495cdbe390c
-- title:
--   Weighted occupation above a level is the integral over the ray after strict passage
-- statement:
--   The strict upper level set agrees with the open ray after the clock except possibly at its Lebesgue-null endpoint. This extends the proved discounted-tail result to arbitrary nonnegative weights.
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

theorem Kyprianou.Ch05.monotoneStrictPassageWeightedOccupationV1
    (f : NNReal → ℝ) (hm : Monotone f) (x : ℝ) (hx : 0 ≤ x) (hz : f 0 = 0)
    (T : ENNReal)
    (hT : T = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t}))
    (g : ℝ → ENNReal) :
    (∫⁻ t in Ici (0 : ℝ), if x < f t.toNNReal then g t else 0 ∂volume) =
      if T ≠ ⊤ then ∫⁻ t in Ioi T.toReal, g t ∂volume else 0 := by
  sorry
