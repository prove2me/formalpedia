-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_re_dotProduct_diagonal_mulVec_star
-- name    : GlobalTheory.Inertia.re_dotProduct_diagonal_mulVec_star
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:23:12.394234+00:00
-- url     : https://prove2.me/theorems/9b78df33-8e26-4e4b-a142-6840ac373695
-- title:
--   Inertia: re dot Product diagonal mul Vec star
-- statement:
--   The Inertia construction uses the re dot Product diagonal mul Vec star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L122-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L122-L126

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

theorem GlobalTheory.Inertia.re_dotProduct_diagonal_mulVec_star (d x : n → ℂ) :
    (x ⬝ᵥ diagonal d *ᵥ star x).re = ∑ k, (d k).re * Complex.normSq (x k) := by sorry
