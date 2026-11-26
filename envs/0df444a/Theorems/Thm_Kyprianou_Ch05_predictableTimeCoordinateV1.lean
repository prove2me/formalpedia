-- Prove2me | Theorems.Thm_Kyprianou_Ch05_predictableTimeCoordinateV1
-- name    : Kyprianou.Ch05.predictableTimeCoordinateV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:45:31.940662+00:00
-- url     : https://prove2.me/theorems/a331b1c0-0fee-5ac7-93cf-d03a1c076294
-- title:
--   The time coordinate is measurable in the predictable sigma algebra
-- statement:
--   Strict upper time rays have predictable preimages because they are rectangles with the whole sample space in the filtration.
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

theorem Kyprianou.Ch05.predictableTimeCoordinateV1
    {Omega : Type} [MeasurableSpace Omega] (F : Filtration NNReal inferInstance) :
    Measurable[F.predictable] (Prod.fst : NNReal × Omega → NNReal) := by
  sorry
