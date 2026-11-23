-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_exists_sum_sub_card_smul_mem
-- name    : GlobalTheory.FreeQuotient.exists_sum_sub_card_smul_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:37.72415+00:00
-- url     : https://prove2.me/theorems/b31c7984-4fc2-4d5c-9bb5-73253171a501
-- title:
--   Free Quotient: exists sum sub card smul mem
-- statement:
--   The Free Quotient construction uses the exists sum sub card smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L216-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L216-L235

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
variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]

theorem GlobalTheory.FreeQuotient.exists_sum_sub_card_smul_mem (P : Ideal A) [P.IsMaximal] (m : M)
    (hm : ∀ g ∈ P.inertia G, g • m - m ∈ P • (⊤ : Submodule A M)) :
    ∃ s : Finset (A × A), ∑ p ∈ s, p.1 • ∑ g : G, g • (p.2 • m) -
      (Nat.card (P.inertia G) : A) • m ∈ P • (⊤ : Submodule A M) := by sorry
