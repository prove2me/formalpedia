-- Prove2me | Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_eq_exp_of_log
-- name    : GlobalTheory.IsAnalyticGroupChart.eq_exp_of_log
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:06.506808+00:00
-- url     : https://prove2.me/theorems/7a62cc41-1ba6-4587-8e82-15e0ab75e3d3
-- title:
--   Is Analytic Group Chart: eq exp of log
-- statement:
--   The Is Analytic Group Chart construction uses the eq exp of log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L461-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L461-L465

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

theorem GlobalTheory.IsAnalyticGroupChart.eq_exp_of_log {e : V →+ A} (he : ∀ᶠ a in 𝓝 (0 : A), e (h.log (φ a)) = a) :
    e = h.exp := by sorry
