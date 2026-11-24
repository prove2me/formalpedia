-- Prove2me | Theorems.Thm_GlobalTheory_WittTrace_exists_isometry_step
-- name    : GlobalTheory.WittTrace.exists_isometry_step
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:56:27.327622+00:00
-- url     : https://prove2.me/theorems/2b2db0a6-8954-4db4-8178-ba2929900aaa
-- title:
--   Witt Trace: exists isometry step
-- statement:
--   The Witt Trace construction uses the exists isometry step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryOfLinearIndependent.lean#L32-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryOfLinearIndependent.lean#L32-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittTrace
open Module Matrix GlobalTheory.HermDiag GlobalTheory.HermWitt
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]

theorem GlobalTheory.WittTrace.exists_isometry_step (hs : ∀ b : E, c b = b → ∃ s : E, s ≠ 0 ∧ s + c s = b)
    (hc : ∀ t, c (c t) = t) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hrep : ∀ ψ : V →ₗ[E] E, ∃ w, ∀ z, B z w = ψ z) (S : Set V) {x y : V}
    (hx : x ∉ Submodule.span E S) (hy : y ∉ Submodule.span E S) (hxy : B x x = B y y)
    (hS : ∀ h ∈ S, B h x = B h y) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ γ x = y ∧ ∀ h ∈ S, γ h = h := by sorry
