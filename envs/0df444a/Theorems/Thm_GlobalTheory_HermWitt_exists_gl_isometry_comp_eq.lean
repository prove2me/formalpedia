-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_comp_eq
-- name    : GlobalTheory.HermWitt.exists_gl_isometry_comp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:36.682193+00:00
-- url     : https://prove2.me/theorems/ecb04520-6f27-4e1e-8fba-8435dbe7b04e
-- title:
--   Herm Witt: exists gl isometry comp eq
-- statement:
--   The Herm Witt construction uses the exists gl isometry comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L339-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L339-L355

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
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n] [DecidableEq n]

theorem GlobalTheory.HermWitt.exists_gl_isometry_comp_eq (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) (hdet : G.det ≠ 0)
    {W : Type*} [AddCommGroup W] [Module E W] {g f : W →ₗ[E] (n → E)}
    (h0 : ∀ a, g a = 0 ↔ f a = 0)
    (hgf : ∀ a b, f a ⬝ᵥ G *ᵥ (c ∘ f b) = g a ⬝ᵥ G *ᵥ (c ∘ g b)) :
    ∃ γ : GL n E,
      (∀ z w, ((γ : Matrix n n E) *ᵥ z) ⬝ᵥ G *ᵥ (c ∘ ((γ : Matrix n n E) *ᵥ w)) =
        z ⬝ᵥ G *ᵥ (c ∘ w)) ∧ ∀ a, (γ : Matrix n n E) *ᵥ g a = f a := by sorry
