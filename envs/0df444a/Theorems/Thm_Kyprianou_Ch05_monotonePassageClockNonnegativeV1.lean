-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotonePassageClockNonnegativeV1
-- name    : Kyprianou.Ch05.monotonePassageClockNonnegativeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:49:23.81851+00:00
-- url     : https://prove2.me/theorems/ea382579-70ba-447a-bbca-0a7a1fa385bc
-- title:
--   Measurable strict passage clock including level zero
-- statement:
--   The previously proved rational clock construction also works at zero. The origin is excluded from the strict upper set by the nonnegative level and zero initial value.
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

theorem Kyprianou.Ch05.monotonePassageClockNonnegativeV1
    (x : ℝ) (hx : 0 ≤ x) :
    ∃ T : (NNReal → ℝ) → ENNReal, Measurable T ∧
      ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        T f = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t}) := by
  sorry
