-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_exists_congr_diagonal
-- name    : GlobalTheory.HermDiag.exists_congr_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:39.778888+00:00
-- url     : https://prove2.me/theorems/e5dabc85-cd40-4d38-87be-c8a83e9eb76e
-- title:
--   Herm Diag: exists congr diagonal
-- statement:
--   The Herm Diag construction uses the exists congr diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L213-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L213-L220

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

theorem GlobalTheory.HermDiag.exists_congr_diagonal (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) :
    ∃ (P : Matrix n n E) (d : n → E), P.det ≠ 0 ∧ Pᵀ * G * P.map c = Matrix.diagonal d ∧
      (∀ i, c (d i) = d i) ∧ (G.det ≠ 0 → ∀ i, d i ≠ 0) := by sorry
