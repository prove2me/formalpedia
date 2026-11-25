-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_mulVec_eq_herm
-- name    : GlobalTheory.HermWitt.exists_gl_isometry_mulVec_eq_herm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:17.039884+00:00
-- url     : https://prove2.me/theorems/35990756-86ec-596c-8fcf-217f88f8b3ce
-- title:
--   Herm Witt: exists gl isometry mul Vec eq herm
-- statement:
--   The Herm Witt construction uses the exists gl isometry mul Vec eq herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L453-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L453-L463

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
open NumberField ReciprocityTheory.ChartRestriction.G
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.HermWitt.exists_gl_isometry_mulVec_eq_herm {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) {x y : Fin r → E}
    (hxy : FD.herm G x x = FD.herm G y y) (hx : FD.herm G x x ≠ 0) :
    ∃ γ : GL (Fin r) E,
      (∀ z w, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ z)
        ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = FD.herm G z w) ∧
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ x = y ∧
      ∀ u, FD.herm G u x = 0 → FD.herm G u y = 0 → (γ : Matrix (Fin r) (Fin r) E) *ᵥ u = u := by sorry
