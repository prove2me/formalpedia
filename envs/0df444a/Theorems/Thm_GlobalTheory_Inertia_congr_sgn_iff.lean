-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_congr_sgn_iff
-- name    : GlobalTheory.Inertia.congr_sgn_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:11.98808+00:00
-- url     : https://prove2.me/theorems/0b33eaf9-f93f-4917-895f-ab229aefa2fc
-- title:
--   Inertia: congr sgn iff
-- statement:
--   The Inertia construction uses the congr sgn iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L385-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L385-L394

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

theorem GlobalTheory.Inertia.congr_sgn_iff {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0)
    (p : ℕ) :
    (p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ↔
      p = posIndex G := by sorry
