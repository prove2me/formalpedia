-- Prove2me | Theorems.Thm_GlobalTheory_LocalLift_exists_admissible_isUnit_det
-- name    : GlobalTheory.LocalLift.exists_admissible_isUnit_det
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:14:07.015463+00:00
-- url     : https://prove2.me/theorems/2101bc03-5838-4f46-bb81-e2665d5eb757
-- title:
--   Local Lift: exists admissible is Unit det
-- statement:
--   The Local Lift construction uses the exists admissible is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdmissibleIsUnitDetLocalInvolution.lean#L131-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdmissibleIsUnitDetLocalInvolution.lean#L131-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleLagrangianTransverseFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleIsUnitDetLocalInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.LocalLift

theorem GlobalTheory.LocalLift.exists_admissible_isUnit_det :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by sorry
