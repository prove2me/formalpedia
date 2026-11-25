-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_extend
-- name    : GlobalTheory.HermWitt.exists_isometry_extend
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:19.768665+00:00
-- url     : https://prove2.me/theorems/5204b2f3-b34f-52f7-b46d-fd6a121500b3
-- title:
--   Herm Witt: exists isometry extend
-- statement:
--   The Herm Witt construction uses the exists isometry extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L258-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L258-L264

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

theorem GlobalTheory.HermWitt.exists_isometry_extend [FiniteDimensional E V] (h2 : (2 : E) ≠ 0)
    (hc : ∀ t, c (c t) = t) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) {U U' : Submodule E V} (f : U ≃ₗ[E] U')
    (hf : ∀ a b : U, B (f a) (f b) = B a b) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ a : U, γ a = f a := by sorry
