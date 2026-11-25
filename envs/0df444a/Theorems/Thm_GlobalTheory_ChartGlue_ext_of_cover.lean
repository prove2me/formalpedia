-- Prove2me | Theorems.Thm_GlobalTheory_ChartGlue_ext_of_cover
-- name    : GlobalTheory.ChartGlue.ext_of_cover
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:17.497679+00:00
-- url     : https://prove2.me/theorems/70371974-ab83-4104-828a-acab43de90f7
-- title:
--   Chart Glue: ext of cover
-- statement:
--   The Chart Glue construction uses the ext of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ChartMeasApplyOfSubset.lean#L131-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ChartMeasApplyOfSubset.lean#L131-L137

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff ENNReal
open GlobalTheory GlobalTheory.ChartGlue
variable {n : ℕ} {X : Type*} [TopologicalSpace X] {ι : Type*}
variable [MeasurableSpace X]
variable [BorelSpace X]
variable [SecondCountableTopology X]

theorem GlobalTheory.ChartGlue.ext_of_cover {μ ν : Measure X} (S : ι → Set X) (hS : ∀ i, IsOpen (S i))
    (hc : ∀ y, ∃ i, y ∈ S i) (h : ∀ i A, MeasurableSet A → A ⊆ S i → μ A = ν A) : μ = ν := by sorry
