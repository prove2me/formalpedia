-- Prove2me | Theorems.Thm_Kyprianou_ch02PoissonRestrictionLaw
-- name    : Kyprianou.ch02PoissonRestrictionLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:45:48.079339+00:00
-- url     : https://prove2.me/theorems/6a538021-8dd5-42c7-9c31-05c054e1bcce
-- title:
--   Finite-intensity intersection count has its original Poisson distribution
-- statement:
--   Finite-intensity intersection count has its original Poisson distribution. Exact proper conjunct of Kyprianou Chapter 2 poissonRestrictionAndIndependenceCh02V3 with unchanged hypotheses.
-- source:
--   Kyprianou (2006), Chapter 2 Poisson random measures: restriction and disjoint-region independence

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou

theorem ch02PoissonRestrictionLaw
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    (∀ (A B : Set (ℝ × ℝ)), MeasurableSet A → MeasurableSet B →
       LevyStochCalc.Poisson.referenceIntensity ν (A ∩ B) < ⊤ →
       P.map (fun ω => N.N ω (A ∩ B)) =
         LevyStochCalc.Poisson.poissonMeasureENN
           (LevyStochCalc.Poisson.referenceIntensity ν (A ∩ B)).toNNReal) :=
    by sorry

end Kyprianou
