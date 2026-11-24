-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_exists_apply_self_ne_zero
-- name    : GlobalTheory.HermDiag.exists_apply_self_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:17.990797+00:00
-- url     : https://prove2.me/theorems/7a5d4b9f-0458-44ec-acb4-7784b55dd667
-- title:
--   Herm Diag: exists apply self ne zero
-- statement:
--   The Herm Diag construction uses the exists apply self ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L26-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermDiag
open Module Matrix
variable {E : Type*} [Field E] {c : E →+* E}

theorem GlobalTheory.HermDiag.exists_apply_self_ne_zero {V : Type*} [AddCommGroup V] [Module E V]
    (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hne : B ≠ 0) : ∃ x, B x x ≠ 0 := by sorry
