-- Prove2me | Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_log_add
-- name    : GlobalTheory.IsAnalyticGroupChart.log_add
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:24.29621+00:00
-- url     : https://prove2.me/theorems/833d64c9-dec8-5d9e-b1c8-2dd6125ae128
-- title:
--   Is Analytic Group Chart: log add
-- statement:
--   The Is Analytic Group Chart construction uses the log add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L437-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L437-L444

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
omit [FiniteDimensional ℂ V]

theorem GlobalTheory.IsAnalyticGroupChart.log_add :
    ∀ᶠ p in 𝓝 (0 : A × A), h.log (φ (p.1 + p.2)) = h.log (φ p.1) + h.log (φ p.2) := by sorry
