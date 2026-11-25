-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_finite_invariants_iff
-- name    : GlobalTheory.FreeQuotient.finite_invariants_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:05:40.523285+00:00
-- url     : https://prove2.me/theorems/df504cb3-0407-55dd-8362-70e24fceb0ea
-- title:
--   Free Quotient: finite invariants iff
-- statement:
--   The Free Quotient construction uses the finite invariants iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L560-L566
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L560-L566

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
variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]

theorem GlobalTheory.FreeQuotient.finite_invariants_iff (h : IsFreeRingAction G A) :
    Module.Finite B (Representation.ofDistribMulAction B G M).invariants ↔ Module.Finite A M := by sorry
