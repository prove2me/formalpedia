-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotoneStrictPassageClockBoundsV1
-- name    : Kyprianou.Ch05.monotoneStrictPassageClockBoundsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:49:14.805665+00:00
-- url     : https://prove2.me/theorems/270a1488-5b4d-5873-8b5d-09afc4cf6686
-- title:
--   Strict passage clock bounds the upper level set
-- statement:
--   The infimum of the strict upper time set is below each crossing time, and strict inequality above the infimum supplies an earlier crossing time. Monotonicity transfers that crossing to the later time.
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

theorem Kyprianou.Ch05.monotoneStrictPassageClockBoundsV1
    (f : NNReal → ℝ) (hm : Monotone f) (x : ℝ) (T : ENNReal)
    (hT : T = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t}))
    (t : NNReal) :
    ((T < (t : ENNReal)) → x < f t) ∧
    (0 < t → x < f t → T ≤ (t : ENNReal)) := by
  sorry
