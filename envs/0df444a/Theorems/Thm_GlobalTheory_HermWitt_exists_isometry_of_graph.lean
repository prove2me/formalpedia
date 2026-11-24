-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_of_graph
-- name    : GlobalTheory.HermWitt.exists_isometry_of_graph
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:20:12.694427+00:00
-- url     : https://prove2.me/theorems/05782748-c008-4874-a559-e6dbd11d9e27
-- title:
--   Herm Witt: exists isometry of graph
-- statement:
--   The Herm Witt construction uses the exists isometry of graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L228-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L228-L246

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

theorem GlobalTheory.HermWitt.exists_isometry_of_graph [FiniteDimensional E V] (h2 : (2 : E) ≠ 0)
    (hc : ∀ t, c (c t) = t) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) (Γ : Submodule E (V × V))
    (h0 : ∀ p ∈ Γ, p.1 = 0 ↔ p.2 = 0) (hΓ : ∀ p ∈ Γ, ∀ q ∈ Γ, B p.2 q.2 = B p.1 q.1) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ p ∈ Γ, γ p.1 = p.2 := by sorry
