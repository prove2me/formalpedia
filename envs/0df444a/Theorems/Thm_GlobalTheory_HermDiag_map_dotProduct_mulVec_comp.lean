-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_map_dotProduct_mulVec_comp
-- name    : GlobalTheory.HermDiag.map_dotProduct_mulVec_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:38.831553+00:00
-- url     : https://prove2.me/theorems/edfbcf87-632f-4a08-8262-99fcdcc5de47
-- title:
--   Herm Diag: map dot Product mul Vec comp
-- statement:
--   The Herm Diag construction uses the map dot Product mul Vec comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L142-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L142-L148

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

theorem GlobalTheory.HermDiag.map_dotProduct_mulVec_comp (hc : ∀ t, c (c t) = t) {G : Matrix n n E}
    (hG : ∀ a b, c (G a b) = G b a) (x y : n → E) :
    c (x ⬝ᵥ G *ᵥ (c ∘ y)) = y ⬝ᵥ G *ᵥ (c ∘ x) := by sorry
