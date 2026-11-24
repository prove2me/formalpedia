-- Prove2me | Theorems.Thm_GlobalTheory_LocalLift_lift_of_field
-- name    : GlobalTheory.LocalLift.lift_of_field
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:14:24.775036+00:00
-- url     : https://prove2.me/theorems/a940f203-fcdf-4379-8778-5dd4ed87d15b
-- title:
--   Local Lift: lift of field
-- statement:
--   The Local Lift construction uses the lift of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdmissibleIsUnitDetLocalInvolution.lean#L21-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdmissibleIsUnitDetLocalInvolution.lean#L21-L129

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

theorem GlobalTheory.LocalLift.lift_of_field
    (hF : ∀ {k : Type} [Field k] (c : k →+* k), (∀ x, c (c x) = x) → (2 : k) ≠ 0 →
      ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) k), IsUnit S.det → Sᵀ = -S.map c →
      ∀ (A C : Matrix (Fin n) (Fin n) k), (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
        Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
        ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by sorry
