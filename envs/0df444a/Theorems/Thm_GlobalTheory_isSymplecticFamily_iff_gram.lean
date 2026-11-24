-- Prove2me | Theorems.Thm_GlobalTheory_isSymplecticFamily_iff_gram
-- name    : GlobalTheory.isSymplecticFamily_iff_gram
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:08.671019+00:00
-- url     : https://prove2.me/theorems/79388d88-da3d-4a12-9dbd-3e86ec96f57b
-- title:
--   Global Theory: is Symplectic Family iff gram
-- statement:
--   The Global Theory construction uses the is Symplectic Family iff gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L411-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L411-L428

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
omit [Fintype l]

theorem GlobalTheory.isSymplecticFamily_iff_gram (hB : B.IsAlt) (v : l ⊕ l → M) :
    IsSymplecticFamily B (fun i => v (.inl i)) (fun i => v (.inr i)) (fun _ => 1) ↔
      (Matrix.of fun i j => B (v i) (v j)) = -Matrix.J l R := by sorry
