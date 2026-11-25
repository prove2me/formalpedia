-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_posIndex_map_eq_card_of_congr_diagonal
-- name    : GlobalTheory.Inertia.posIndex_map_eq_card_of_congr_diagonal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:23:08.3118+00:00
-- url     : https://prove2.me/theorems/a0d639c1-c2ef-4ab4-8855-97137f098e32
-- title:
--   Inertia: pos Index map eq card of congr diagonal
-- statement:
--   The Inertia construction uses the pos Index map eq card of congr diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L487-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L487-L490

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
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem GlobalTheory.Inertia.posIndex_map_eq_card_of_congr_diagonal (τ : E →+* ℂ) {G P : Matrix n n E} {d : n → E}
    (hP : P.det ≠ 0) (hd : Pᵀ * G * P.map FD.cc = diagonal d) :
    posIndex (G.map τ) = (Finset.univ.filter fun k => 0 < (τ (d k)).re).card := by sorry
