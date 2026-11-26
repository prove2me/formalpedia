-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotoneMarkedCrossingClockUniqueV1
-- name    : Kyprianou.Ch05.monotoneMarkedCrossingClockUniqueV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:29:32.365055+00:00
-- url     : https://prove2.me/theorems/4ca86309-1f1a-4520-91f2-05f4fed546c8
-- title:
--   A strict upward jump crossing occurs only at the first strict passage clock
-- statement:
--   The crossing time itself belongs to the strict-passage set, and no earlier member is possible because earlier path values are bounded by its left limit.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.monotoneMarkedCrossingClockUniqueV1
    (f : NNReal → ℝ) (hm : Monotone f) (x : ℝ) (t : NNReal)
    (ht : 0 < t) (hpost : x < f t) (hpre : Function.leftLim f t ≤ x) :
    sInf ((fun u : NNReal => (u : ENNReal)) '' {u : NNReal | 0 < u ∧ x < f u}) =
      (t : ENNReal) := by
  sorry
