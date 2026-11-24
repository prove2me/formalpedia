-- Prove2me | Theorems.Thm_GlobalTheory_ChartGlue_contDiffOn_real
-- name    : GlobalTheory.ChartGlue.contDiffOn_real
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:10:22.238724+00:00
-- url     : https://prove2.me/theorems/4ec6d90d-c524-4bee-aa13-859a979fdd77
-- title:
--   Chart Glue: cont Diff On real
-- statement:
--   The Chart Glue construction uses the cont Diff On real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ChartMeasApplyOfSubset.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ChartMeasApplyOfSubset.lean#L27-L29

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

theorem GlobalTheory.ChartGlue.contDiffOn_real {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) : ContDiffOn ℝ ∞ g U := by sorry
