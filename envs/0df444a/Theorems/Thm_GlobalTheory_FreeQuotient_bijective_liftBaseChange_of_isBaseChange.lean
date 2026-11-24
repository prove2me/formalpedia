-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_bijective_liftBaseChange_of_isBaseChange
-- name    : GlobalTheory.FreeQuotient.bijective_liftBaseChange_of_isBaseChange
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:26.378561+00:00
-- url     : https://prove2.me/theorems/dba6ca13-b625-48e1-ba6d-0a7b40ae0ee4
-- title:
--   Free Quotient: bijective lift Base Change of is Base Change
-- statement:
--   The Free Quotient construction uses the bijective lift Base Change of is Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L422-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L422-L431

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
variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
  (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
omit [Finite G] [MulSemiringAction G A] [SMulCommClass G B A] [FaithfulSMul B A]
  [Algebra.IsInvariant B A G] [SMulDistribClass G A M]

theorem GlobalTheory.FreeQuotient.bijective_liftBaseChange_of_isBaseChange
    (h : IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype) :
    Function.Bijective
      ((Representation.ofDistribMulAction B G M).invariants.subtype.liftBaseChange A) := by sorry
