-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_extend
-- name    : GlobalTheory.HermWitt.exists_gl_isometry_extend
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:33.090923+00:00
-- url     : https://prove2.me/theorems/d02cad93-1286-4854-8d36-693d905c0bc1
-- title:
--   Herm Witt: exists gl isometry extend
-- statement:
--   The Herm Witt construction uses the exists gl isometry extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L357-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L357-L366

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

theorem GlobalTheory.HermWitt.exists_gl_isometry_extend (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) (hdet : G.det ≠ 0)
    {U U' : Submodule E (n → E)} (f : U ≃ₗ[E] U')
    (hf : ∀ a b : U, (f a : n → E) ⬝ᵥ G *ᵥ (c ∘ (f b : n → E)) =
      (a : n → E) ⬝ᵥ G *ᵥ (c ∘ (b : n → E))) :
    ∃ γ : GL n E,
      (∀ z w, ((γ : Matrix n n E) *ᵥ z) ⬝ᵥ G *ᵥ (c ∘ ((γ : Matrix n n E) *ᵥ w)) =
        z ⬝ᵥ G *ᵥ (c ∘ w)) ∧ ∀ a : U, (γ : Matrix n n E) *ᵥ (a : n → E) = f a := by sorry
