-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_isGreatest_negIndex
-- name    : GlobalTheory.Inertia.isGreatest_negIndex
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:21.820938+00:00
-- url     : https://prove2.me/theorems/f9f06b3e-8452-4667-a5d5-4d45c2dd3abd
-- title:
--   Inertia: is Greatest neg Index
-- statement:
--   The Inertia construction uses the is Greatest neg Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L34-L38

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

theorem GlobalTheory.Inertia.isGreatest_negIndex (G : Matrix n n ℂ) :
    IsGreatest {d | ∃ W : Submodule ℂ (n → ℂ), finrank ℂ W = d ∧
      ∀ x ∈ W, x ≠ 0 → (x ⬝ᵥ G *ᵥ star x).re < 0} (negIndex G) := by sorry
