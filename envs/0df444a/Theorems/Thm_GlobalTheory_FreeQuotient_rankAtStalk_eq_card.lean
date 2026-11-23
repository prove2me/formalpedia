-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_rankAtStalk_eq_card
-- name    : GlobalTheory.FreeQuotient.rankAtStalk_eq_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:57.652881+00:00
-- url     : https://prove2.me/theorems/b0f08356-fe4c-46b4-b1e8-eea77c078e2c
-- title:
--   Free Quotient: rank At Stalk eq card
-- statement:
--   The Free Quotient construction uses the rank At Stalk eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L517-L527
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L517-L527

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
variable {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A]
variable [Finite G] (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]

theorem GlobalTheory.FreeQuotient.rankAtStalk_eq_card (h : IsFreeRingAction G A) (p : PrimeSpectrum B) :
    Module.rankAtStalk A p = Nat.card G := by sorry
