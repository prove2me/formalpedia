-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_posIndex_eq_card_of_congr_diagonal
-- name    : GlobalTheory.Inertia.posIndex_eq_card_of_congr_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:06.282799+00:00
-- url     : https://prove2.me/theorems/2db0edcb-c6d1-44ed-bd2d-f5ce8d7dc761
-- title:
--   Inertia: pos Index eq card of congr diagonal
-- statement:
--   The Inertia construction uses the pos Index eq card of congr diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L167-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L167-L170

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

theorem GlobalTheory.Inertia.posIndex_eq_card_of_congr_diagonal {G P : Matrix n n ℂ} {d : n → ℂ} (hP : P.det ≠ 0)
    (hd : Pᵀ * G * P.map conj = diagonal d) :
    posIndex G = (Finset.univ.filter fun k => 0 < (d k).re).card := by sorry
