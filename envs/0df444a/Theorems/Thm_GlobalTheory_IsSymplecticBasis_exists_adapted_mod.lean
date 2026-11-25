-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_exists_adapted_mod
-- name    : GlobalTheory.IsSymplecticBasis.exists_adapted_mod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:22:23.564211+00:00
-- url     : https://prove2.me/theorems/14b372dd-5503-402e-aa30-9e04592a2f26
-- title:
--   Is Symplectic Basis: exists adapted mod
-- statement:
--   The Is Symplectic Basis construction uses the exists adapted mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L595-L628
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L595-L628

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
open TensorProduct
variable {S R Λ l : Type*} [CommRing S] [CommRing R] [AddCommGroup Λ] [Module S Λ] [Fintype l]
  {B : LinearMap.BilinForm S Λ}

theorem GlobalTheory.IsSymplecticBasis.exists_adapted_mod [Finite (MaximalSpectrum R)] {f : S →+* R}
    (hf : Surjective f) (hB : B.IsAlt) {b : Basis (l ⊕ l) S Λ} (hb : IsSymplecticBasis B b)
    {P Q : Submodule S Λ} (hIP : RingHom.ker f • ⊤ ≤ P) (hIQ : RingHom.ker f • ⊤ ≤ Q)
    (hP : ∀ x ∈ P, ∀ y ∈ P, f (B x y) = 0) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, f (B x y) = 0)
    (hPQ : P ⊔ Q = ⊤) :
    ∃ c : Basis (l ⊕ l) S Λ, IsSymplecticBasis B c ∧
      (∀ x, x ∈ P ↔ ∀ i, f (c.repr x (.inr i)) = 0) ∧
      ∀ x, x ∈ Q ↔ ∀ i, f (c.repr x (.inl i)) = 0 := by sorry
