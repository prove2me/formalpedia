-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_exists_congr_iff_posIndex_eq
-- name    : GlobalTheory.Inertia.exists_congr_iff_posIndex_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:15.635127+00:00
-- url     : https://prove2.me/theorems/33168c6f-ea29-4b06-b21b-b21b20141d64
-- title:
--   Inertia: exists congr iff pos Index eq
-- statement:
--   The Inertia construction uses the exists congr iff pos Index eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L328-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L328-L344

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

theorem GlobalTheory.Inertia.exists_congr_iff_posIndex_eq {G H : Matrix n n ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0)
    (hH : H.IsHermitian) (hH0 : H.det ≠ 0) :
    (∃ P : Matrix n n ℂ, P.det ≠ 0 ∧ Pᵀ * G * P.map conj = H) ↔ posIndex G = posIndex H := by sorry
