-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_descent_of_invariant_dual_basis
-- name    : GlobalTheory.FreeQuotient.descent_of_invariant_dual_basis
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:39.670619+00:00
-- url     : https://prove2.me/theorems/ea253e6a-3b8b-4cb0-bff3-a12daabcd990
-- title:
--   Free Quotient: descent of invariant dual basis
-- statement:
--   The Free Quotient construction uses the descent of invariant dual basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L349-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L349-L380

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
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]
variable (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
omit [Fintype G] [SMulDistribClass G A M]

theorem GlobalTheory.FreeQuotient.descent_of_invariant_dual_basis {n : ℕ} (v : Fin n → M) (f : Fin n → M →ₗ[A] A)
    (hv : ∀ i (g : G), g • v i = v i) (hf : ∀ i (g : G) m, f i (g • m) = g • f i m)
    (hfv : ∀ m, ∑ i, f i m • v i = m) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype ∧
      Module.Finite B (Representation.ofDistribMulAction B G M).invariants ∧
      Module.Projective B (Representation.ofDistribMulAction B G M).invariants := by sorry
