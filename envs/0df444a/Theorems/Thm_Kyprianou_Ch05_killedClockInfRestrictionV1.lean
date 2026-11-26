-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedClockInfRestrictionV1
-- name    : Kyprianou.Ch05.killedClockInfRestrictionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:29:32.330337+00:00
-- url     : https://prove2.me/theorems/cb333218-b785-4664-bfe0-4a251b96d3e2
-- title:
--   Infimum restricted to times before death
-- statement:
--   An infimum below death is unchanged by restriction, since the restricted set has a member below death. Otherwise the restricted set is empty.
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

theorem Kyprianou.Ch05.killedClockInfRestrictionV1
    (S : Set ENNReal) (e : ENNReal) :
    sInf (S ∩ Iio e) = if sInf S < e then sInf S else ⊤ := by
  sorry
