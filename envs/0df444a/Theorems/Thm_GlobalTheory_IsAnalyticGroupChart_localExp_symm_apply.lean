-- Prove2me | Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_localExp_symm_apply
-- name    : GlobalTheory.IsAnalyticGroupChart.localExp_symm_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:12:12.60508+00:00
-- url     : https://prove2.me/theorems/b0b93021-68f0-4fb0-a1d5-c28a18da72fa
-- title:
--   Is Analytic Group Chart: local Exp symm apply
-- statement:
--   The Is Analytic Group Chart construction uses the local Exp symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L392-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L392-L392

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

theorem GlobalTheory.IsAnalyticGroupChart.localExp_symm_apply (a : A) : h.localExp.symm a = h.log (φ a) := by sorry
