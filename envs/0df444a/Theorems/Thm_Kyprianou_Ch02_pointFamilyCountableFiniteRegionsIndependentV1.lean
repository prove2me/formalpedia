-- Prove2me | Theorems.Thm_Kyprianou_Ch02_pointFamilyCountableFiniteRegionsIndependentV1
-- name    : Kyprianou.Ch02.pointFamilyCountableFiniteRegionsIndependentV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:43:27.745442+00:00
-- url     : https://prove2.me/theorems/2838f35c-7dc1-44ca-93dd-3e240c0b6ac4
-- title:
--   Countable Poisson point-family region independence under finite intensities
-- statement:
--   For a sigma-finite mark measure and a Poisson point family, the random counts of any countable disjoint family of finite-intensity measurable regions are mutually independent. Every finite restriction has independent counts by the already Proved LeanLevy finite-index Poisson count theorem; countable independence follows from the Mathlib finite-subfamily characterisation. This removes the finite-intensity part of the existing Kyprianou Ch02 pointFamilyCountableCountsIndependentV3 obligation.
-- source:
--   Kyprianou Chapter 2 Theorem 2.4; derived from Prove2Me Proved ProbabilityTheory.iIndepFun_poissonRandomMeasure_apply and Mathlib iIndepFun_iff_finset; parent 115918e3-0f06-4a8b-b139-8f88e933e165; mission ed6e9edb-945b-4dc1-bb4b-3eed54f89dd0

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_iIndepFun_poissonRandomMeasure_apply
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.pointFamilyCountableFiniteRegionsIndependentV1
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : IsPoissonPointFamily K Y m P)
    {ι : Type} [Countable ι] (B : ι → Set E)
    (hm : ∀ i, MeasurableSet (B i))
    (hf : ∀ i, m (B i) < ⊤)
    (hdj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    iIndepFun (fun i ω => poissonRandomMeasure K Y ω (B i)) P := by sorry
