-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_of_orthogonal
-- name    : GlobalTheory.HermWitt.exists_isometry_of_orthogonal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:20:11.239868+00:00
-- url     : https://prove2.me/theorems/0f3e8bfb-34be-43ea-924b-9de07ba7e7ec
-- title:
--   Herm Witt: exists isometry of orthogonal
-- statement:
--   The Herm Witt construction uses the exists isometry of orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L83-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L83-L107

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

theorem GlobalTheory.HermWitt.exists_isometry_of_orthogonal (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) {ι : Type*} [Finite ι] {x y : ι → V}
    (hx : ∀ i j, i ≠ j → B (x i) (x j) = 0) (hy : ∀ i j, i ≠ j → B (y i) (y j) = 0)
    (hxy : ∀ i, B (x i) (x i) = B (y i) (y i)) (hne : ∀ i, B (x i) (x i) ≠ 0) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ i, γ (x i) = y i := by sorry
