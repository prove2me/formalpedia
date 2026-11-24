-- Prove2me | Theorems.Thm_GlobalTheory_LocalNorm_exists_eq_sq_add_of_mul_eq
-- name    : GlobalTheory.LocalNorm.exists_eq_sq_add_of_mul_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:13:57.376574+00:00
-- url     : https://prove2.me/theorems/517bac9b-4878-4e66-a965-7d218931072e
-- title:
--   Local Norm: exists eq sq add of mul eq
-- statement:
--   The Local Norm construction uses the exists eq sq add of mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsBinaryEqAdicCompletion.lean#L153-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsBinaryEqAdicCompletion.lean#L153-L160

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LocalNorm

theorem GlobalTheory.LocalNorm.exists_eq_sq_add_of_mul_eq {K : Type*} [Field K] {d x a₀ b₀ a₁ b₁ a₂ b₂ : K}
    (h₁ : a₁ ^ 2 + d * b₁ ^ 2 ≠ 0)
    (h : x * (a₁ ^ 2 + d * b₁ ^ 2) = (a₀ ^ 2 + d * b₀ ^ 2) * (a₂ ^ 2 + d * b₂ ^ 2)) :
    ∃ a b, x = a ^ 2 + d * b ^ 2 := by sorry
