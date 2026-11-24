-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_finRankTrace_smul
-- name    : GlobalTheory.OpTrace.finRankTrace_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:31.07801+00:00
-- url     : https://prove2.me/theorems/5ae6f678-665c-4f7e-bbbf-58770f9e23df
-- title:
--   Op Trace: fin Rank Trace smul
-- statement:
--   The Op Trace construction uses the fin Rank Trace smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L553-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L553-L558

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.OpTrace.finRankTrace_smul (c : ℂ) (T : V →ₗ[ℂ] V) [FiniteDimensional ℂ (LinearMap.range T)] :
    finRankTrace (c • T) = c * finRankTrace T := by sorry
