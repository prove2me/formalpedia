-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_admissible_isUnit_det_local_involution
-- name    : GlobalTheory.T.exists_admissible_isUnit_det_local_involution
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:28.704051+00:00
-- url     : https://prove2.me/theorems/fafc9ae2-4ce2-5119-8a63-82f4eb8c4a4a
-- title:
--   T: exists admissible is Unit det local involution
-- statement:
--   The T construction uses the exists admissible is Unit det local involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdmissibleIsUnitDetLocalInvolutionStatement.lean#L6-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdmissibleIsUnitDetLocalInvolutionStatement.lean#L6-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleIsUnitDetLocalInvolution
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleIsUnitDetLocalInvolutionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_admissible_isUnit_det_local_involution : ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by sorry
