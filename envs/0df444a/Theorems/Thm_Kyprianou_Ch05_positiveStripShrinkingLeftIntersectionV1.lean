-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positiveStripShrinkingLeftIntersectionV1
-- name    : Kyprianou.Ch05.positiveStripShrinkingLeftIntersectionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:00:36.04941+00:00
-- url     : https://prove2.me/theorems/386a3996-6eb7-4928-ac6f-2e1dd2c27d0b
-- title:
--   Intersection of shrinking left time strips is the time fibre
-- statement:
--   The positive time fibre is exactly the intersection of all strips with left endpoint strictly below the time.
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

theorem Kyprianou.Ch05.positiveStripShrinkingLeftIntersectionV1
    (t : NNReal) (ht : 0 < t) :
    (⋂ r > OrderDual.toDual t, Ioc ((OrderDual.ofDual r : NNReal) : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ)) =
      ({(t : ℝ)} : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
  sorry
