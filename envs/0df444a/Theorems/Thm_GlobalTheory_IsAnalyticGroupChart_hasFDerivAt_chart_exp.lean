-- Prove2me | Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_hasFDerivAt_chart_exp
-- name    : GlobalTheory.IsAnalyticGroupChart.hasFDerivAt_chart_exp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:17:43.540464+00:00
-- url     : https://prove2.me/theorems/d8086e19-4b5b-45b2-a93d-9f6bd59f7f8f
-- title:
--   Is Analytic Group Chart: has FDeriv At chart exp
-- statement:
--   The Is Analytic Group Chart construction uses the has FDeriv At chart exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L457-L459
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L457-L459

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

theorem GlobalTheory.IsAnalyticGroupChart.hasFDerivAt_chart_exp :
    HasFDerivAt (fun v => φ (h.exp v)) (ContinuousLinearMap.id ℂ V) 0 := by sorry
