-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_exists_congr_diagonal_herm
-- name    : GlobalTheory.HermDiag.exists_congr_diagonal_herm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:16.713564+00:00
-- url     : https://prove2.me/theorems/b2460a04-84f9-475b-b03f-0be51c5eec26
-- title:
--   Herm Diag: exists congr diagonal herm
-- statement:
--   The Herm Diag construction uses the exists congr diagonal herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L249-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L249-L255

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
open NumberField ReciprocityTheory.ChartRestriction.G
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.HermDiag.exists_congr_diagonal_herm {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) :
    ∃ (P : Matrix (Fin r) (Fin r) E) (d : Fin r → E), P.det ≠ 0 ∧
      Pᵀ * G * P.map FD.cc = Matrix.diagonal d ∧
      (∀ i, FD.cc (d i) = d i) ∧ (G.det ≠ 0 → ∀ i, d i ≠ 0) := by sorry
