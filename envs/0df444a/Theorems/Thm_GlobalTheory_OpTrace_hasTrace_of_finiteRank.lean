-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_hasTrace_of_finiteRank
-- name    : GlobalTheory.OpTrace.hasTrace_of_finiteRank
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:39.885313+00:00
-- url     : https://prove2.me/theorems/76c0edcd-2db9-42ab-8875-2521baeecc11
-- title:
--   Op Trace: has Trace of finite Rank
-- statement:
--   The Op Trace construction uses the has Trace of finite Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L580-L589
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L580-L589

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

theorem GlobalTheory.OpTrace.hasTrace_of_finiteRank {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) [FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H))] :
    HasTrace T (finRankTrace (T : H →ₗ[ℂ] H)) := by sorry
