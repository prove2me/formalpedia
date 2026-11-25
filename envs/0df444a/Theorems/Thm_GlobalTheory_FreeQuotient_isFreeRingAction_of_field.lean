-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_isFreeRingAction_of_field
-- name    : GlobalTheory.FreeQuotient.isFreeRingAction_of_field
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:05:34.808708+00:00
-- url     : https://prove2.me/theorems/c359e516-6022-4f0b-9eb6-e2fce89c34f6
-- title:
--   Free Quotient: is Free Ring Action of field
-- statement:
--   The Free Quotient construction uses the is Free Ring Action of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L44-L52

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
open GlobalTheory.FreeQuotient
variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]

theorem GlobalTheory.FreeQuotient.isFreeRingAction_of_field (K : Type*) [Field K] [MulSemiringAction G K]
    [FaithfulSMul G K] : IsFreeRingAction G K := by sorry
