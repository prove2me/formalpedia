-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_of_apply_sub_ne_zero
-- name    : GlobalTheory.HermWitt.exists_isometry_of_apply_sub_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:19.392803+00:00
-- url     : https://prove2.me/theorems/891d3e5d-2ce2-4287-97f5-338a3d0e3b4a
-- title:
--   Herm Witt: exists isometry of apply sub ne zero
-- statement:
--   The Herm Witt construction uses the exists isometry of apply sub ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L37-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L37-L55

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

theorem GlobalTheory.HermWitt.exists_isometry_of_apply_sub_ne_zero {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) {x y : V} (hxy : B x x = B y y) (ha : B x (x - y) ≠ 0) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ γ x = y ∧
      ∀ u, B u (x - y) = 0 → γ u = u := by sorry
