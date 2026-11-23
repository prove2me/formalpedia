-- Prove2me | Theorems.Thm_Kyprianou_Ch02_pointFamilyCountableCountsIndependentV3
-- name    : Kyprianou.Ch02.pointFamilyCountableCountsIndependentV3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T07:27:51.427814+00:00
-- url     : https://prove2.me/theorems/115918e3-0f06-4a8b-b139-8f88e933e165
-- title:
--   Countably many disjoint Poisson point-family regions have mutually independent counts
-- statement:
--   Countably many disjoint Poisson point-family regions have mutually independent counts This is an exact conjunct of the accepted residual theorem f8ff2134-db5d-427a-8b3a-338579d5ee6f, required for Poisson random-measure existence in Kyprianou Chapter 2. Its hypotheses and conclusion retain the original generic arbitrary measurable-space assumptions.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.4; full PRM existence residual f8ff2134-db5d-427a-8b3a-338579d5ee6f, original Prove2Me decomposition.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem pointFamilyCountableCountsIndependentV3
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    ∀ {ι : Type} [Countable ι] (A : ι → Set E),
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       ProbabilityTheory.iIndepFun
         (fun i (ω : Ω) => ProbabilityTheory.poissonRandomMeasure K Y ω (A i)) P := by sorry
end Kyprianou.Ch02
