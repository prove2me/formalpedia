-- Prove2me | Theorems.Thm_GlobalTheory_FreeQuotient_exists_invariant_dual_basis
-- name    : GlobalTheory.FreeQuotient.exists_invariant_dual_basis
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:57.534212+00:00
-- url     : https://prove2.me/theorems/0b9bb74f-4d68-4c59-aeb7-1378c50c889b
-- title:
--   Free Quotient: exists invariant dual basis
-- statement:
--   The Free Quotient construction uses the exists invariant dual basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L315-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L315-L341

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

theorem GlobalTheory.FreeQuotient.exists_invariant_dual_basis [Module.Finite A M] [Module.Projective A M]
    {c : A} (hc : ∑ g : G, g • c = 1)
    (hM : Submodule.span A {m : M | ∀ g : G, g • m = m} = ⊤) :
    ∃ (n : ℕ) (v : Fin n → M) (f : Fin n → M →ₗ[A] A), (∀ i (g : G), g • v i = v i) ∧
      (∀ i (g : G) m, f i (g • m) = g • f i m) ∧ ∀ m, ∑ i, f i m • v i = m := by sorry
