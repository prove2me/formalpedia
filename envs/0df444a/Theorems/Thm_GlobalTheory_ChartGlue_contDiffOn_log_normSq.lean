-- Prove2me | Theorems.Thm_GlobalTheory_ChartGlue_contDiffOn_log_normSq
-- name    : GlobalTheory.ChartGlue.contDiffOn_log_normSq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:40.676411+00:00
-- url     : https://prove2.me/theorems/236f6f7c-b954-4362-8fed-4d0bf7bf1cdc
-- title:
--   Chart Glue: cont Diff On log norm Sq
-- statement:
--   The Chart Glue construction uses the cont Diff On log norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ChartMeasApplyOfSubset.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ChartMeasApplyOfSubset.lean#L31-L34

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

theorem GlobalTheory.ChartGlue.contDiffOn_log_normSq {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (h0 : ∀ v ∈ U, g v ≠ 0) :
    ContDiffOn ℝ ∞ (fun v => Real.log (‖g v‖ ^ 2)) U := by sorry
