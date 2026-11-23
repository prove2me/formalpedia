-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_isSymplecticFamily_iff_toMatrix_mem
-- name    : GlobalTheory.IsSymplecticBasis.isSymplecticFamily_iff_toMatrix_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:57.301985+00:00
-- url     : https://prove2.me/theorems/307bb741-814c-4368-bc8f-340173df6f0d
-- title:
--   Is Symplectic Basis: is Symplectic Family iff to Matrix mem
-- statement:
--   The Is Symplectic Basis construction uses the is Symplectic Family iff to Matrix mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L430-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L430-L443

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

theorem GlobalTheory.IsSymplecticBasis.isSymplecticFamily_iff_toMatrix_mem {b : Basis (l ⊕ l) R M}
    (hb : IsSymplecticBasis B b) (hB : B.IsAlt) (v : l ⊕ l → M) :
    IsSymplecticFamily B (fun i => v (.inl i)) (fun i => v (.inr i)) (fun _ => 1) ↔
      b.toMatrix v ∈ symplecticGroup l R := by sorry
