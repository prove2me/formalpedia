-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_exists_congr_sgn
-- name    : GlobalTheory.Inertia.exists_congr_sgn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:19.503418+00:00
-- url     : https://prove2.me/theorems/010e4982-d184-43bb-8268-f4bd7d3f0bb1
-- title:
--   Inertia: exists congr sgn
-- statement:
--   The Inertia construction uses the exists congr sgn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L379-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L379-L383

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

theorem GlobalTheory.Inertia.exists_congr_sgn {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0) :
    ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn (posIndex G) a : ℝ) : ℂ) := by sorry
