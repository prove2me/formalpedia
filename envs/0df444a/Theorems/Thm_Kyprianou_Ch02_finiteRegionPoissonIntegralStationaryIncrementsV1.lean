-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonIntegralStationaryIncrementsV1
-- name    : Kyprianou.Ch02.finiteRegionPoissonIntegralStationaryIncrementsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T09:00:08.92158+00:00
-- url     : https://prove2.me/theorems/bb711a08-f4ab-46c6-90dd-e092ed7f7b3b
-- title:
--   Lemma 2.8: Stationary law of the finite-window Poisson mark integral
-- statement:
--   Stationary law of the finite-window Poisson mark integral. Use translation invariance of referenceIntensity and the Poisson character/mark-law identity.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.8; direct decomposition of canonical finiteRegionPoissonIntegralCh02V3 (38df877c-0872-40d5-8b33-bbad3487ba47).

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem finiteRegionPoissonIntegralStationaryIncrementsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ProbabilityTheory.HasStationaryIncrements
      (fun t ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P := by sorry
end Kyprianou.Ch02
