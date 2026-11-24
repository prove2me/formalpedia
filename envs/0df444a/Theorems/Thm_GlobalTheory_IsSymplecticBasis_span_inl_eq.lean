-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_span_inl_eq
-- name    : GlobalTheory.IsSymplecticBasis.span_inl_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:21:56.845308+00:00
-- url     : https://prove2.me/theorems/375d8aa8-23e2-498b-9c56-8049d074073e
-- title:
--   Is Symplectic Basis: span inl eq
-- statement:
--   The Is Symplectic Basis construction uses the span inl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L476-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L476-L482

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

theorem GlobalTheory.IsSymplecticBasis.span_inl_eq {b : Basis (l ⊕ l) R M} (hb : IsSymplecticBasis B b)
    {P : Submodule R M} (hP : ∀ x ∈ P, ∀ y ∈ P, B x y = 0) (h : ∀ i, b (.inl i) ∈ P) :
    Submodule.span R (Set.range fun i => b (.inl i)) = P := by sorry
