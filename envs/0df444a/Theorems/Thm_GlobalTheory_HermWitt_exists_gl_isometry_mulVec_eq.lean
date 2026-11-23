-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_mulVec_eq
-- name    : GlobalTheory.HermWitt.exists_gl_isometry_mulVec_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:13.130149+00:00
-- url     : https://prove2.me/theorems/34dc26d6-f2be-4f2e-8c64-59e0ac928c85
-- title:
--   Herm Witt: exists gl isometry mul Vec eq
-- statement:
--   The Herm Witt construction uses the exists gl isometry mul Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L306-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L306-L320

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

theorem GlobalTheory.HermWitt.exists_gl_isometry_mulVec_eq (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) {x y : n → E}
    (hxy : x ⬝ᵥ G *ᵥ (c ∘ x) = y ⬝ᵥ G *ᵥ (c ∘ y)) (hx : x ⬝ᵥ G *ᵥ (c ∘ x) ≠ 0) :
    ∃ γ : GL n E,
      (∀ z w, ((γ : Matrix n n E) *ᵥ z) ⬝ᵥ G *ᵥ (c ∘ ((γ : Matrix n n E) *ᵥ w)) =
        z ⬝ᵥ G *ᵥ (c ∘ w)) ∧ (γ : Matrix n n E) *ᵥ x = y ∧
      ∀ u, u ⬝ᵥ G *ᵥ (c ∘ x) = 0 → u ⬝ᵥ G *ᵥ (c ∘ y) = 0 → (γ : Matrix n n E) *ᵥ u = u := by sorry
