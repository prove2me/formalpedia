-- Prove2me | Theorems.Thm_Kyprianou_ch02PoissonDisjointRegionSigmaIndep
-- name    : Kyprianou.ch02PoissonDisjointRegionSigmaIndep
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T20:45:46.946193+00:00
-- url     : https://prove2.me/theorems/1f07b91d-5803-4028-afb6-125a37da230b
-- title:
--   Evaluation sigma algebras of disjoint regions are independent
-- statement:
--   Evaluation sigma algebras of disjoint regions are independent. Exact proper conjunct of Kyprianou Chapter 2 poissonRestrictionAndIndependenceCh02V3 with unchanged hypotheses.
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

theorem ch02PoissonDisjointRegionSigmaIndep
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    (∀ (A B : Set (ℝ × ℝ)), MeasurableSet A →
      MeasurableSet B → Disjoint A B →
      ProbabilityTheory.Indep
        (⨆ C ∈ {C : Set (ℝ × ℝ) |
             C ⊆ A ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)
        (⨆ D ∈ {D : Set (ℝ × ℝ) |
             D ⊆ B ∧ MeasurableSet D},
          MeasurableSpace.comap (fun ω => N.N ω D) inferInstance)
        P) :=
    by sorry

end Kyprianou
