-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_dotProduct_mulVec_comp_eq_sum
-- name    : GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:36.106182+00:00
-- url     : https://prove2.me/theorems/22c4fa18-b1aa-4dd4-adea-e9c48196037d
-- title:
--   Herm Diag: dot Product mul Vec comp eq sum
-- statement:
--   The Herm Diag construction uses the dot Product mul Vec comp eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L132-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L132-L134

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

theorem GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum (c : E → E) (G : Matrix n n E) (x y : n → E) :
    x ⬝ᵥ G *ᵥ (c ∘ y) = ∑ a, ∑ b, x a * G a b * c (y b) := by sorry
