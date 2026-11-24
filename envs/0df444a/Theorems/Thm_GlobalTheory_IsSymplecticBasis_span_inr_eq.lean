-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_span_inr_eq
-- name    : GlobalTheory.IsSymplecticBasis.span_inr_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:21:08.157789+00:00
-- url     : https://prove2.me/theorems/880a13e5-e574-46b1-b970-489b3667ada3
-- title:
--   Is Symplectic Basis: span inr eq
-- statement:
--   The Is Symplectic Basis construction uses the span inr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L485-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L485-L491

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

theorem GlobalTheory.IsSymplecticBasis.span_inr_eq {b : Basis (l ⊕ l) R M} (hb : IsSymplecticBasis B b)
    {Q : Submodule R M} (hQ : ∀ x ∈ Q, ∀ y ∈ Q, B x y = 0) (h : ∀ i, b (.inr i) ∈ Q) :
    Submodule.span R (Set.range fun i => b (.inr i)) = Q := by sorry
