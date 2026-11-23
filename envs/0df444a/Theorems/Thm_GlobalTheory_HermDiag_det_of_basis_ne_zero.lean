-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_det_of_basis_ne_zero
-- name    : GlobalTheory.HermDiag.det_of_basis_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:19.508725+00:00
-- url     : https://prove2.me/theorems/592c60b3-872f-405b-99cc-88e227cac6dc
-- title:
--   Herm Diag: det of basis ne zero
-- statement:
--   The Herm Diag construction uses the det of basis ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L181-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L181-L188

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

theorem GlobalTheory.HermDiag.det_of_basis_ne_zero (v : Basis n E (n → E)) :
    (Matrix.of fun k i => v i k).det ≠ 0 := by sorry
