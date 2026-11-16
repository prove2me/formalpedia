-- Prove2me | Theorems.Thm_Kyprianou_poissonRestrictionAndIndependenceCh02V3
-- name    : Kyprianou.poissonRestrictionAndIndependenceCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:21:10.363118+00:00
-- url     : https://prove2.me/theorems/6830f96f-6fae-45ec-98db-e480818ea924
-- title:
--   Corollary 2.5: restriction and independence on disjoint Poisson regions
-- statement:
--   Restricting a Poisson random measure to a measurable region produces Poisson counts with the restricted intensity; disjoint measurable subregions yield mutually independent evaluations. The restriction is the actual restricted measure, not an unrelated postulated random process.
-- source:
--   Kyprianou (2006), Corollary 2.5, p. 40

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou

theorem poissonRestrictionAndIndependenceCh02V3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    (∀ (A B : Set (ℝ × ℝ)), MeasurableSet A → MeasurableSet B →
       LevyStochCalc.Poisson.referenceIntensity ν (A ∩ B) < ⊤ →
       P.map (fun ω => N.N ω (A ∩ B)) =
         LevyStochCalc.Poisson.poissonMeasureENN
           (LevyStochCalc.Poisson.referenceIntensity ν (A ∩ B)).toNNReal) ∧
    (∀ {ι : Type} [Countable ι]
       (A : ι → Set (ℝ × ℝ)) (B : Set (ℝ × ℝ)),
       MeasurableSet B →
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       (∀ i, A i ⊆ B) →
       ProbabilityTheory.iIndepFun
          (fun i (ω : Ω) => (N.N ω).restrict B (A i)) P) ∧
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
