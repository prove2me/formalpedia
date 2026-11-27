-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_LinearChart_continuous_rightModulus
-- name    : GroundTheory.Automorphic.Measures.LinearChart.continuous_rightModulus
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:26.70541+00:00
-- url     : https://prove2.me/theorems/8c16451b-beb2-58eb-b600-f1b415ba67f2
-- title:
--   Linear Chart: continuous right Modulus
-- statement:
--   The Linear Chart construction uses the continuous right Modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresChart.lean#L214-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresChart.lean#L214-L217

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
open GroundTheory.Automorphic.Measures.LinearChart
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type*} [Fintype ι]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] (C : LinearChart F ι G)
variable (μ₀ : Measure (ι → F)) [μ₀.IsAddHaarMeasure]
variable [LocallyCompactSpace G]
variable [T2Space G] [TotallyDisconnectedSpace G]

theorem GroundTheory.Automorphic.Measures.LinearChart.continuous_rightModulus : Continuous C.rightModulus := by sorry
