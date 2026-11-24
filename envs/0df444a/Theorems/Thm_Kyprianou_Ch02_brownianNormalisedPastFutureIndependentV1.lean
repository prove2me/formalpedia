-- Prove2me | Theorems.Thm_Kyprianou_Ch02_brownianNormalisedPastFutureIndependentV1
-- name    : Kyprianou.Ch02.brownianNormalisedPastFutureIndependentV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:50:15.961177+00:00
-- url     : https://prove2.me/theorems/9f7972ce-46ad-4694-9558-8af5245ec110
-- title:
--   Brownian past-future independence survives subtraction of the initial value
-- statement:
--   For any BrownianMotion B and times 0≤s<t, the shifted Brownian sample paths W_t-W_0 have a natural past sigma-field independent of their future increment. The shifted past is measurable relative to the original Brownian past (since W_0 is in the original past) and future increments agree pathwise. Supports the corrected normalised independent Brownian and Poisson drivers Chapter 2 mission.
-- source:
--   Kyprianou (2006), Chapter 2, normalisation of Brownian driver

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

theorem Kyprianou.Ch02.brownianNormalisedPastFutureIndependentV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P) :
    ∀ {s t : ℝ}, 0 ≤ s → s < t →
      Indep
        (⨆ j ∈ Set.Iic s,
          MeasurableSpace.comap (fun ω => B.W j ω - B.W 0 ω) inferInstance)
        (MeasurableSpace.comap
          (fun ω => (B.W t ω - B.W 0 ω) - (B.W s ω - B.W 0 ω))
          inferInstance)
        P := by sorry
