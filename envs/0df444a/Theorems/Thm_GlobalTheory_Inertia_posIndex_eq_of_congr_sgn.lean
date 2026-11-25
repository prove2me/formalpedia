-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_posIndex_eq_of_congr_sgn
-- name    : GlobalTheory.Inertia.posIndex_eq_of_congr_sgn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:23:14.7358+00:00
-- url     : https://prove2.me/theorems/ea77172c-ebd0-41d8-99b9-e40d18e94df5
-- title:
--   Inertia: pos Index eq of congr sgn
-- statement:
--   The Inertia construction uses the pos Index eq of congr sgn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L373-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L373-L377

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
variable {r s : ℕ}

theorem GlobalTheory.Inertia.posIndex_eq_of_congr_sgn {G P : Matrix (Fin r) (Fin r) ℂ} {p : ℕ} (hp : p ≤ r)
    (hP : P.det ≠ 0)
    (h : Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) :
    posIndex G = p := by sorry
