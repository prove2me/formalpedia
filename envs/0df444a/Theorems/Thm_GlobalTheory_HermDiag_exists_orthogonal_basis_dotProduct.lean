-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_dotProduct
-- name    : GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:07.320579+00:00
-- url     : https://prove2.me/theorems/9adba0c3-6d83-454e-b41f-604c464eb594
-- title:
--   Herm Diag: exists orthogonal basis dot Product
-- statement:
--   The Herm Diag construction uses the exists orthogonal basis dot Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L159-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L159-L167

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
variable [DecidableEq n]

theorem GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) :
    ∃ v : Basis n E (n → E), ∀ i j, i ≠ j → v i ⬝ᵥ G *ᵥ (c ∘ v j) = 0 := by sorry
