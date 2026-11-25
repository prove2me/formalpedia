-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_posIndex_neg_eq_sub
-- name    : GlobalTheory.Inertia.posIndex_neg_eq_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:28.73713+00:00
-- url     : https://prove2.me/theorems/3de9ccc8-5dd1-4ca8-a548-f6bdd2732de7
-- title:
--   Inertia: pos Index neg eq sub
-- statement:
--   The Inertia construction uses the pos Index neg eq sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L209-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L209-L213

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

theorem GlobalTheory.Inertia.posIndex_neg_eq_sub {G : Matrix n n ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0) :
    posIndex (-G) = Fintype.card n - posIndex G := by sorry
