-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_negIndex_eq_card_eigenvalues
-- name    : GlobalTheory.Inertia.negIndex_eq_card_eigenvalues
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:01.652478+00:00
-- url     : https://prove2.me/theorems/b8d0a431-30d7-5054-89c6-4357dbe1ad7c
-- title:
--   Inertia: neg Index eq card eigenvalues
-- statement:
--   The Inertia construction uses the neg Index eq card eigenvalues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L240-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L240-L244

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

theorem GlobalTheory.Inertia.negIndex_eq_card_eigenvalues {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    negIndex G = (Finset.univ.filter fun k => hG.eigenvalues k < 0).card := by sorry
