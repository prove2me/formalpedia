-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_exists_congr_diagonal_eigenvalues
-- name    : GlobalTheory.Inertia.exists_congr_diagonal_eigenvalues
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:39.467919+00:00
-- url     : https://prove2.me/theorems/4a729fc6-d651-4cb0-89e3-670eb2e4f6db
-- title:
--   Inertia: exists congr diagonal eigenvalues
-- statement:
--   The Inertia construction uses the exists congr diagonal eigenvalues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L215-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L215-L232

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

theorem GlobalTheory.Inertia.exists_congr_diagonal_eigenvalues {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    ∃ P : Matrix n n ℂ, P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal fun k => (hG.eigenvalues k : ℂ) := by sorry
