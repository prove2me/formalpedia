-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_posIndex_submatrix_equiv
-- name    : GlobalTheory.Inertia.posIndex_submatrix_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:20.186062+00:00
-- url     : https://prove2.me/theorems/1a3c351a-7742-4334-a20e-d584a3830971
-- title:
--   Inertia: pos Index submatrix equiv
-- statement:
--   The Inertia construction uses the pos Index submatrix equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L73-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L73-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]

theorem GlobalTheory.Inertia.posIndex_submatrix_equiv (G : Matrix n n ℂ) (e : m ≃ n) :
    posIndex (G.submatrix e e) = posIndex G := by sorry
