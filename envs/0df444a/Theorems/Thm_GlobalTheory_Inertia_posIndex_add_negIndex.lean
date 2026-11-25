-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_posIndex_add_negIndex
-- name    : GlobalTheory.Inertia.posIndex_add_negIndex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:57.314467+00:00
-- url     : https://prove2.me/theorems/2965525b-0fb8-484b-8080-0d73883c18b3
-- title:
--   Inertia: pos Index add neg Index
-- statement:
--   The Inertia construction uses the pos Index add neg Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L204-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L204-L207

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
variable [DecidableEq n]

theorem GlobalTheory.Inertia.posIndex_add_negIndex {G : Matrix n n ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0) :
    posIndex G + negIndex G = Fintype.card n := by sorry
