-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_comp_eq_of_nondegenerate
-- name    : GlobalTheory.HermWitt.exists_isometry_comp_eq_of_nondegenerate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:27.727974+00:00
-- url     : https://prove2.me/theorems/837da231-7e13-4e66-8c64-0e57c01b02c5
-- title:
--   Herm Witt: exists isometry comp eq of nondegenerate
-- statement:
--   The Herm Witt construction uses the exists isometry comp eq of nondegenerate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L109-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L109-L132

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

theorem GlobalTheory.HermWitt.exists_isometry_comp_eq_of_nondegenerate (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {g f : W →ₗ[E] V} (hgf : ∀ a b, B (f a) (f b) = B (g a) (g b))
    (hW : ∀ a, (∀ b, B (g b) (g a) = 0) → a = 0) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ a, γ (g a) = f a := by sorry
