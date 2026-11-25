-- Prove2me | Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_analyticAt_chart_exp
-- name    : GlobalTheory.IsAnalyticGroupChart.analyticAt_chart_exp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:17:24.831129+00:00
-- url     : https://prove2.me/theorems/ac6bb90e-4565-4be6-bf45-46603861fd29
-- title:
--   Is Analytic Group Chart: analytic At chart exp
-- statement:
--   The Is Analytic Group Chart construction uses the analytic At chart exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L454-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L454-L455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [AddCommGroup A]
  [TopologicalSpace A]
open GlobalTheory.IsAnalyticGroupChart
variable {φ : OpenPartialHomeomorph A V} (h : IsAnalyticGroupChart φ)
include h
variable [IsTopologicalAddGroup A]
variable [FiniteDimensional ℂ V] [CompleteSpace V]

theorem GlobalTheory.IsAnalyticGroupChart.analyticAt_chart_exp : AnalyticAt ℂ (fun v => φ (h.exp v)) 0 := by sorry
