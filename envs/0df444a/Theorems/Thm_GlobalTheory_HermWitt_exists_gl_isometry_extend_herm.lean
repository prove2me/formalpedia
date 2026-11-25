-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_extend_herm
-- name    : GlobalTheory.HermWitt.exists_gl_isometry_extend_herm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:16.177582+00:00
-- url     : https://prove2.me/theorems/5b376048-fbcc-5b8c-99d6-316d9c29a52e
-- title:
--   Herm Witt: exists gl isometry extend herm
-- statement:
--   The Herm Witt construction uses the exists gl isometry extend herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L474-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L474-L484

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

theorem GlobalTheory.HermWitt.exists_gl_isometry_extend_herm {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) (hdet : G.det ≠ 0)
    {U U' : Submodule E (Fin r → E)} (f : U ≃ₗ[E] U')
    (hf : ∀ a b : U, FD.herm G (f a) (f b) = FD.herm G a b) :
    ∃ γ : GL (Fin r) E,
      (∀ z w, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ z)
        ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = FD.herm G z w) ∧
      ∀ a : U, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) = f a := by sorry
