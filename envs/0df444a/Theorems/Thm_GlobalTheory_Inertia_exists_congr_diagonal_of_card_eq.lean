-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_exists_congr_diagonal_of_card_eq
-- name    : GlobalTheory.Inertia.exists_congr_diagonal_of_card_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:43.601212+00:00
-- url     : https://prove2.me/theorems/59532ddd-e7b1-4f55-9e64-7149ba2edbe2
-- title:
--   Inertia: exists congr diagonal of card eq
-- statement:
--   The Inertia construction uses the exists congr diagonal of card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L293-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L293-L326

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

theorem GlobalTheory.Inertia.exists_congr_diagonal_of_card_eq {G : Matrix n n ℂ} (hG : G.IsHermitian)
    (hG0 : G.det ≠ 0) {e : n → ℝ} (he : ∀ k, e k ≠ 0)
    (hcard : (Finset.univ.filter fun k => 0 < e k).card = posIndex G) :
    ∃ P : Matrix n n ℂ, P.det ≠ 0 ∧ Pᵀ * G * P.map conj = diagonal fun k => (e k : ℂ) := by sorry
