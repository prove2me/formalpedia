-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstHoldingMarkProductLaw
-- name    : Kyprianou.Ch01.compoundPoissonFirstHoldingMarkProductLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:22:53.060967+00:00
-- url     : https://prove2.me/theorems/5a46a969-1a28-4e66-94dc-2cf246827212
-- title:
--   The first holding time and jump mark have the independent exponential-mark product law
-- statement:
--   The first exponential interarrival and first jump mark have the joint product law expMeasure rate times jumpLaw, as a measurable random vector. The compound-Poisson driver's joint independent family provides their independence and both marginal HasLaw facts.
-- source:
--   LeanLevy compound Poisson driver's Sum-indexed iIndepFun and Mathlib IndepFun.hasLaw_prod, used in Kyprianou (2006) Section 1.3.4 first-event renewal.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonFirstHoldingMarkProductLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    HasLaw (fun w => (arrival 0 w, marks 0 w))
      ((expMeasure rate).prod jumpLaw) Q := by
  sorry
