-- Prove2me | Theorems.Thm_GlobalTheory_isFreeRingAction_translationAction
-- name    : GlobalTheory.isFreeRingAction_translationAction
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:09.167504+00:00
-- url     : https://prove2.me/theorems/86dbf12f-584f-511b-afa4-4b866a04251d
-- title:
--   Global Theory: is Free Ring Action translation Action
-- statement:
--   The Global Theory construction uses the is Free Ring Action translation Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L778-L782
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L778-L782

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
universe w v u
open CategoryTheory

theorem GlobalTheory.isFreeRingAction_translationAction (G R : Type*) [Group G] [Finite G] [CommRing R] :
    letI := translationAction G R
    IsFreeRingAction G (G → R) := by sorry
