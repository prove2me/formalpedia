-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_exists_finset_inertia
-- name    : GlobalTheory.FreeQuotient.exists_finset_inertia
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:37.194914+00:00
-- url     : https://prove2.me/theorems/d98a2d6f-09b2-4334-a0e3-a9ddc5b89dac
-- title:
--   Free Quotient: exists finset inertia
-- statement:
--   The Free Quotient construction uses the exists finset inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L144-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L144-L154

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
variable (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
variable {G A}

theorem GlobalTheory.FreeQuotient.exists_finset_inertia [Finite G] (P : Ideal A) [hP : P.IsMaximal] :
    ∃ s : Finset (A × A), (∀ g ∉ P.inertia G, ∑ p ∈ s, p.1 * g • p.2 = 0) ∧
      ∀ h ∈ P.inertia G, ∑ p ∈ s, p.1 * h • p.2 - 1 ∈ P := by sorry
