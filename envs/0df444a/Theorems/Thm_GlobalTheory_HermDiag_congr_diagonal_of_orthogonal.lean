-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_congr_diagonal_of_orthogonal
-- name    : GlobalTheory.HermDiag.congr_diagonal_of_orthogonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:12.48597+00:00
-- url     : https://prove2.me/theorems/0bd44c2b-058c-4c44-b906-a000fa70a5ab
-- title:
--   Herm Diag: congr diagonal of orthogonal
-- statement:
--   The Herm Diag construction uses the congr diagonal of orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L200-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L200-L211

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

theorem GlobalTheory.HermDiag.congr_diagonal_of_orthogonal {G : Matrix n n E} (c : E → E) (v : n → n → E)
    (hv : ∀ i j, i ≠ j → v i ⬝ᵥ G *ᵥ (c ∘ v j) = 0) :
    (Matrix.of fun k i => v i k)ᵀ * G * (Matrix.of fun k i => v i k).map c =
      Matrix.diagonal fun i => v i ⬝ᵥ G *ᵥ (c ∘ v i) := by sorry
