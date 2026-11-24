-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_dotProduct_apply_eq
-- name    : GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct_apply_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:19:23.513701+00:00
-- url     : https://prove2.me/theorems/30be4fef-edc4-4632-a8f1-ad6eb699dd33
-- title:
--   Herm Diag: exists orthogonal basis dot Product apply eq
-- statement:
--   The Herm Diag construction uses the exists orthogonal basis dot Product apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L169-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L169-L179

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

theorem GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct_apply_eq (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) {x : n → E}
    (hx : x ⬝ᵥ G *ᵥ (c ∘ x) ≠ 0) (i₀ : n) :
    ∃ v : Basis n E (n → E), v i₀ = x ∧ ∀ i j, i ≠ j → v i ⬝ᵥ G *ᵥ (c ∘ v j) = 0 := by sorry
