-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_exists_adapted
-- name    : GlobalTheory.IsSymplecticBasis.exists_adapted
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:22:02.634223+00:00
-- url     : https://prove2.me/theorems/dbcb012a-989d-4135-a840-2d5abc042aa3
-- title:
--   Is Symplectic Basis: exists adapted
-- statement:
--   The Is Symplectic Basis construction uses the exists adapted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L495-L526
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L495-L526

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
variable {R M l : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype l] [DecidableEq l]
  {B : LinearMap.BilinForm R M}
omit [DecidableEq l]

theorem GlobalTheory.IsSymplecticBasis.exists_adapted [Finite (MaximalSpectrum R)] {b : Basis (l ⊕ l) R M}
    (hb : IsSymplecticBasis B b) (hB : B.IsAlt) {P Q : Submodule R M}
    (hP : ∀ x ∈ P, ∀ y ∈ P, B x y = 0) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, B x y = 0) (hPQ : P ⊔ Q = ⊤) :
    ∃ c : Basis (l ⊕ l) R M, IsSymplecticBasis B c ∧ (∀ i, c (.inl i) ∈ P) ∧
      ∀ i, c (.inr i) ∈ Q := by sorry
