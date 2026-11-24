-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_exists_sum_smul_eq_one
-- name    : GlobalTheory.FreeQuotient.exists_sum_smul_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:42.146258+00:00
-- url     : https://prove2.me/theorems/318c66da-220a-459e-babe-c7681a32e19c
-- title:
--   Free Quotient: exists sum smul eq one
-- statement:
--   The Free Quotient construction uses the exists sum smul eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L239-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L239-L257

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
variable (G A)

theorem GlobalTheory.FreeQuotient.exists_sum_smul_eq_one
    (h : ∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P) :
    ∃ c : A, ∑ g : G, g • c = 1 := by sorry
