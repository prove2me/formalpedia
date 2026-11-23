-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_transpose_mul_mul_map_apply
-- name    : GlobalTheory.HermDiag.transpose_mul_mul_map_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:20.103278+00:00
-- url     : https://prove2.me/theorems/14b2dec8-1924-4076-a3b2-b34f6876b855
-- title:
--   Herm Diag: transpose mul mul map apply
-- statement:
--   The Herm Diag construction uses the transpose mul mul map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L136-L140

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
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n]

theorem GlobalTheory.HermDiag.transpose_mul_mul_map_apply {m : Type*} (c : E → E) (G : Matrix n n E) (P : Matrix n m E)
    (a b : m) :
    (Pᵀ * G * P.map c) a b = (fun k => P k a) ⬝ᵥ G *ᵥ (c ∘ fun k => P k b) := by sorry
