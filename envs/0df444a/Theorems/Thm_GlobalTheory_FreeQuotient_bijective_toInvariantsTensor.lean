-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_bijective_toInvariantsTensor
-- name    : GlobalTheory.FreeQuotient.bijective_toInvariantsTensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:06.839172+00:00
-- url     : https://prove2.me/theorems/20b38c54-0341-42ef-8c63-37eee15390ef
-- title:
--   Free Quotient: bijective to Invariants Tensor
-- statement:
--   The Free Quotient construction uses the bijective to Invariants Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L667-L671
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L667-L671

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
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass B G A]
  (N : Type*) [AddCommGroup N] [Module B N]
variable [SMulCommClass G B A]
variable [FaithfulSMul B A] [Algebra.IsInvariant B A G]
variable {G A}

theorem GlobalTheory.FreeQuotient.bijective_toInvariantsTensor [Finite G] (h : IsFreeRingAction G A) :
    Function.Bijective (toInvariantsTensor G A B N) := by sorry
