-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_existsUnique_equivariant_extension
-- name    : GlobalTheory.FreeQuotient.existsUnique_equivariant_extension
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:41:02.469797+00:00
-- url     : https://prove2.me/theorems/276c68ad-b4db-4bb9-a1aa-f48b06953d07
-- title:
--   Free Quotient: exists Unique equivariant extension
-- statement:
--   The Free Quotient construction uses the exists Unique equivariant extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L592-L608
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L592-L608

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
  {B : Type*} [CommRing B] [Algebra B A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]
  [Module B N] [IsScalarTower B A N] [SMulCommClass G B N]

theorem GlobalTheory.FreeQuotient.existsUnique_equivariant_extension
    (hb : IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype)
    (φ : (Representation.ofDistribMulAction B G M).invariants →ₗ[B]
      (Representation.ofDistribMulAction B G N).invariants) :
    ∃! f : M →ₗ[A] N, (∀ (g : G) m, f (g • m) = g • f m) ∧
      ∀ x : (Representation.ofDistribMulAction B G M).invariants, f x = φ x := by sorry
