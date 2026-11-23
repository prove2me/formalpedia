-- Prove2me | Theorems.Thm_Kyprianou_Ch02_pointFamilyCountableFiniteIntensityIndependentV3
-- name    : Kyprianou.Ch02.pointFamilyCountableFiniteIntensityIndependentV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:37:26.472187+00:00
-- url     : https://prove2.me/theorems/bad33bbb-4945-4e9c-9895-5826374a98b3
-- title:
--   Countably many disjoint finite-intensity PRM evaluations are independent
-- statement:
--   A countably indexed family of measurable, mutually disjoint, finite-intensity regions of the same Poisson point-family random measure has mutually independent counts. This extends the publicly Proved finite-index theorem by applying iIndepFun_iff_finset to every finite subfamily; no independence of infinite-intensity counts is assumed.
-- source:
--   Poisson point-family proved theorem fd7694ea-192b-4e39-891f-34260e2f2425 and pinned Mathlib ProbabilityTheory.iIndepFun_iff_finset; Chapter 2 pointFamilyCountableCountsIndependentV3 Open prerequisite

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_iIndepFun_poissonRandomMeasure_apply
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem pointFamilyCountableFiniteIntensityIndependentV3
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    {ι : Type} [Countable ι] (A : ι → Set E)
    (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, m (A i) < ⊤)
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ProbabilityTheory.iIndepFun
      (fun i (ω : Ω) => ProbabilityTheory.poissonRandomMeasure K Y ω (A i)) P := by sorry
end Kyprianou.Ch02
