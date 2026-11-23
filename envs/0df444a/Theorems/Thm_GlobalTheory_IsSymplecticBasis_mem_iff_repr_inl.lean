-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_mem_iff_repr_inl
-- name    : GlobalTheory.IsSymplecticBasis.mem_iff_repr_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:12:20.683561+00:00
-- url     : https://prove2.me/theorems/e2c1963a-b5b9-4b52-aad9-114f545064e0
-- title:
--   Is Symplectic Basis: mem iff repr inl
-- statement:
--   The Is Symplectic Basis construction uses the mem iff repr inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L468-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L468-L473

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

theorem GlobalTheory.IsSymplecticBasis.mem_iff_repr_inl {b : Basis (l ⊕ l) R M} (hb : IsSymplecticBasis B b)
    {Q : Submodule R M} (hQ : ∀ x ∈ Q, ∀ y ∈ Q, B x y = 0) (h : ∀ i, b (.inr i) ∈ Q) (x : M) :
    x ∈ Q ↔ ∀ i, b.repr x (.inl i) = 0 := by sorry
