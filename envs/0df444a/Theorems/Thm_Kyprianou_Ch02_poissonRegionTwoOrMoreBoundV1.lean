-- Prove2me | Theorems.Thm_Kyprianou_Ch02_poissonRegionTwoOrMoreBoundV1
-- name    : Kyprianou.Ch02.poissonRegionTwoOrMoreBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:52:08.39382+00:00
-- url     : https://prove2.me/theorems/fc3ece9b-1dd7-4721-9009-9fc7156e395d
-- title:
--   A finite-intensity Poisson region has probability of multiple points bounded by squared intensity
-- statement:
--   A finite-intensity Poisson region has probability of multiple points bounded by squared intensity
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1

import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem poissonRegionTwoOrMoreBoundV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hR : MeasurableSet R)
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤) :
    (P {ω | 1 < N.N ω R}).toReal ≤
      (LevyStochCalc.Poisson.referenceIntensity ν R).toReal ^ 2 := by sorry
end Kyprianou.Ch02
