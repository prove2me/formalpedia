-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_finite_projective_invariants_iff
-- name    : GlobalTheory.FreeQuotient.finite_projective_invariants_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:43.045689+00:00
-- url     : https://prove2.me/theorems/ad0c1871-1e31-4e72-bbd4-a3a05a31e887
-- title:
--   Free Quotient: finite projective invariants iff
-- statement:
--   The Free Quotient construction uses the finite projective invariants iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L568-L579
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L568-L579

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

theorem GlobalTheory.FreeQuotient.finite_projective_invariants_iff (h : IsFreeRingAction G A) :
    (Module.Finite B (Representation.ofDistribMulAction B G M).invariants ∧
      Module.Projective B (Representation.ofDistribMulAction B G M).invariants) ↔
    (Module.Finite A M ∧ Module.Projective A M) := by sorry
