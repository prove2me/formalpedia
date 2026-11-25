-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_isFreeRingAction_iff_inertia_eq_bot_of_isPrime
-- name    : GlobalTheory.FreeQuotient.isFreeRingAction_iff_inertia_eq_bot_of_isPrime
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:05:19.038864+00:00
-- url     : https://prove2.me/theorems/38428fe0-e1df-5302-a9e8-f74318fea9bc
-- title:
--   Free Quotient: is Free Ring Action iff inertia eq bot of is Prime
-- statement:
--   The Free Quotient construction uses the is Free Ring Action iff inertia eq bot of is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L36-L42

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

theorem GlobalTheory.FreeQuotient.isFreeRingAction_iff_inertia_eq_bot_of_isPrime :
    IsFreeRingAction G A ↔ ∀ P : Ideal A, P.IsPrime → P.inertia G = ⊥ := by sorry
