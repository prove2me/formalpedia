-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_tame_descent
-- name    : GlobalTheory.FreeQuotient.tame_descent
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:58.6298+00:00
-- url     : https://prove2.me/theorems/46e886a9-9099-4b78-a5d9-d9f21e4c16d2
-- title:
--   Free Quotient: tame descent
-- statement:
--   The Free Quotient construction uses the tame descent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L392-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L392-L402

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

theorem GlobalTheory.FreeQuotient.tame_descent [Module.Finite A M] [Module.Projective A M]
    (h : ∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P)
    (hM : ∀ P : Ideal A, P.IsMaximal → ∀ g ∈ P.inertia G, ∀ m : M,
      g • m - m ∈ P • (⊤ : Submodule A M)) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype ∧
      Module.Finite B (Representation.ofDistribMulAction B G M).invariants ∧
      Module.Projective B (Representation.ofDistribMulAction B G M).invariants := by sorry
