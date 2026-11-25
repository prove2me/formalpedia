-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_witt_theorem
-- name    : GlobalTheory.HermWitt.witt_theorem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:31.421214+00:00
-- url     : https://prove2.me/theorems/5418c90a-7aff-4eb0-aec8-42f333bb75b1
-- title:
--   Herm Witt: witt theorem
-- statement:
--   The Herm Witt construction uses the witt theorem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L488-L512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L488-L512

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag

theorem GlobalTheory.HermWitt.witt_theorem {E : Type*} [Field E] (h2 : (2 : E) ≠ 0) (c : E →+* E)
    (hc : ∀ t, c (c t) = t) {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, c (G a b) = G b a) :
    (∀ x y : Fin r → E, x ⬝ᵥ G *ᵥ (c ∘ x) = y ⬝ᵥ G *ᵥ (c ∘ y) → x ⬝ᵥ G *ᵥ (c ∘ x) ≠ 0 →
      ∃ γ : GL (Fin r) E,
        (∀ z w, ((γ : Matrix (Fin r) (Fin r) E) *ᵥ z) ⬝ᵥ G *ᵥ
          (c ∘ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) = z ⬝ᵥ G *ᵥ (c ∘ w)) ∧
        (γ : Matrix (Fin r) (Fin r) E) *ᵥ x = y) ∧
    (∀ {s : ℕ} (D : Matrix (Fin s) (Fin s) E), (∀ a b, c (D a b) = D b a) → D.det ≠ 0 →
      ∀ G' : Matrix (Fin r) (Fin r) E,
        (∃ P : Matrix (Fin s ⊕ Fin r) (Fin s ⊕ Fin r) E, P.det ≠ 0 ∧
          fromBlocks D 0 0 G' = Pᵀ * fromBlocks D 0 0 G * P.map c) →
        ∃ Q : Matrix (Fin r) (Fin r) E, Q.det ≠ 0 ∧ G' = Qᵀ * G * Q.map c) ∧
    (G.det ≠ 0 → ∀ (U U' : Submodule E (Fin r → E)) (f : U ≃ₗ[E] U'),
      (∀ a b : U, (f a : Fin r → E) ⬝ᵥ G *ᵥ (c ∘ (f b : Fin r → E)) =
        (a : Fin r → E) ⬝ᵥ G *ᵥ (c ∘ (b : Fin r → E))) →
      ∃ γ : GL (Fin r) E,
        (∀ z w, ((γ : Matrix (Fin r) (Fin r) E) *ᵥ z) ⬝ᵥ G *ᵥ
          (c ∘ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) = z ⬝ᵥ G *ᵥ (c ∘ w)) ∧
        ∀ a : U, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) = f a) := by sorry
