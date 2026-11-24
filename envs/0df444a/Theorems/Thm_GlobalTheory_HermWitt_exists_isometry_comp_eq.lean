-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_comp_eq
-- name    : GlobalTheory.HermWitt.exists_isometry_comp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:47.351381+00:00
-- url     : https://prove2.me/theorems/9e68e3bb-628d-4ff6-9576-286bc71e67bb
-- title:
--   Herm Witt: exists isometry comp eq
-- statement:
--   The Herm Witt construction uses the exists isometry comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L248-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L248-L256

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
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]

theorem GlobalTheory.HermWitt.exists_isometry_comp_eq [FiniteDimensional E V] (h2 : (2 : E) ≠ 0)
    (hc : ∀ t, c (c t) = t) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) {W : Type*} [AddCommGroup W] [Module E W]
    {g f : W →ₗ[E] V} (h0 : ∀ a, g a = 0 ↔ f a = 0)
    (hgf : ∀ a b, B (f a) (f b) = B (g a) (g b)) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ a, γ (g a) = f a := by sorry
