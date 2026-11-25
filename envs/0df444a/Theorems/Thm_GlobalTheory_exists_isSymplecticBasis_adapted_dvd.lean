-- Prove2me | Theorems.Thm_GlobalTheory_exists_isSymplecticBasis_adapted_dvd
-- name    : GlobalTheory.exists_isSymplecticBasis_adapted_dvd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:21.899926+00:00
-- url     : https://prove2.me/theorems/c256ccb1-8914-4d13-8a00-31821cf00aa3
-- title:
--   Global Theory: exists is Symplectic Basis adapted dvd
-- statement:
--   The Global Theory construction uses the exists is Symplectic Basis adapted dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L653-L673
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L653-L673

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
variable {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {B : LinearMap.BilinForm ℤ Λ}

theorem GlobalTheory.exists_isSymplecticBasis_adapted_dvd (hB : B.IsAlt) (hp : Bijective B) {g : ℕ}
    (hg : finrank ℤ Λ = 2 * g) {N : ℕ} (hN : N ≠ 0) {P Q : Submodule ℤ Λ}
    (hNP : ∀ x, (N : ℤ) • x ∈ P) (hNQ : ∀ x, (N : ℤ) • x ∈ Q)
    (hP : ∀ x ∈ P, ∀ y ∈ P, (N : ℤ) ∣ B x y) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, (N : ℤ) ∣ B x y)
    (hPQ : P ⊔ Q = ⊤) :
    ∃ c : Basis (Fin g ⊕ Fin g) ℤ Λ, IsSymplecticBasis B c ∧
      (∀ x, x ∈ P ↔ ∀ i, (N : ℤ) ∣ c.repr x (.inr i)) ∧
      ∀ x, x ∈ Q ↔ ∀ i, (N : ℤ) ∣ c.repr x (.inl i) := by sorry
