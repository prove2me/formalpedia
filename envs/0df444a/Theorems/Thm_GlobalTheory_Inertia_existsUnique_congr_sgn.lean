-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_existsUnique_congr_sgn
-- name    : GlobalTheory.Inertia.existsUnique_congr_sgn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:13.553606+00:00
-- url     : https://prove2.me/theorems/fbbb9879-415f-4a2c-bd48-2f3daf83f138
-- title:
--   Inertia: exists Unique congr sgn
-- statement:
--   The Inertia construction uses the exists Unique congr sgn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L396-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L396-L400

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

theorem GlobalTheory.Inertia.existsUnique_congr_sgn {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.IsHermitian)
    (hG0 : G.det ≠ 0) :
    ∃! p : ℕ, p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ) := by sorry
