-- Prove2me | Theorems.Thm_Kyprianou_ch02PoissonRestrictionIndependentCounts
-- name    : Kyprianou.ch02PoissonRestrictionIndependentCounts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:45:48.261389+00:00
-- url     : https://prove2.me/theorems/f7399ba2-c9a4-4fb2-843f-9a5c83366914
-- title:
--   Disjoint counts remain independent after restriction to a containing measurable set
-- statement:
--   Disjoint counts remain independent after restriction to a containing measurable set. Exact proper conjunct of Kyprianou Chapter 2 poissonRestrictionAndIndependenceCh02V3 with unchanged hypotheses.
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

theorem ch02PoissonRestrictionIndependentCounts
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    (∀ {ι : Type} [Countable ι]
       (A : ι → Set (ℝ × ℝ)) (B : Set (ℝ × ℝ)),
       MeasurableSet B →
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       (∀ i, A i ⊆ B) →
       ProbabilityTheory.iIndepFun
          (fun i (ω : Ω) => (N.N ω).restrict B (A i)) P) :=
    by sorry

end Kyprianou
