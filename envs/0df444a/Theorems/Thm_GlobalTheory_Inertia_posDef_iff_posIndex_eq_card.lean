-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_posDef_iff_posIndex_eq_card
-- name    : GlobalTheory.Inertia.posDef_iff_posIndex_eq_card
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:21.473958+00:00
-- url     : https://prove2.me/theorems/bf0dcc2f-2486-57dc-950d-72a8bb918d91
-- title:
--   Inertia: pos Def iff pos Index eq card
-- statement:
--   The Inertia construction uses the pos Def iff pos Index eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L248-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L248-L252

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
open scoped ComplexOrder

theorem GlobalTheory.Inertia.posDef_iff_posIndex_eq_card {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    G.PosDef ↔ posIndex G = Fintype.card n := by sorry
