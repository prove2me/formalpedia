-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_finite_and_projective
-- name    : GlobalTheory.FreeQuotient.finite_and_projective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:50.775751+00:00
-- url     : https://prove2.me/theorems/ba777d73-c69d-4c32-87fe-3424f6e18d2a
-- title:
--   Free Quotient: finite and projective
-- statement:
--   The Free Quotient construction uses the finite and projective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L456-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L456-L466

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

theorem GlobalTheory.FreeQuotient.finite_and_projective (h : IsFreeRingAction G A) :
    Module.Finite B A ∧ Module.Projective B A := by sorry
