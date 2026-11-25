-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_posIndex_eq_card_eigenvalues
-- name    : GlobalTheory.Inertia.posIndex_eq_card_eigenvalues
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:23:08.813113+00:00
-- url     : https://prove2.me/theorems/3e3dd70e-89fc-42b2-b96f-6de1d87070e4
-- title:
--   Inertia: pos Index eq card eigenvalues
-- statement:
--   The Inertia construction uses the pos Index eq card eigenvalues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L234-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L234-L238

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

theorem GlobalTheory.Inertia.posIndex_eq_card_eigenvalues {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    posIndex G = (Finset.univ.filter fun k => 0 < hG.eigenvalues k).card := by sorry
