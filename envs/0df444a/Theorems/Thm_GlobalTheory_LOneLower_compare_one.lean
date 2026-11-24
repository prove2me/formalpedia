-- Prove2me | Theorems.Thm_GlobalTheory_LOneLower_compare_one
-- name    : GlobalTheory.LOneLower.compare_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:01.09761+00:00
-- url     : https://prove2.me/theorems/7b2b5094-0f1b-4941-9369-a3ee627feb6f
-- title:
--   LOne Lower: compare one
-- statement:
--   The LOne Lower construction uses the compare one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L308-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L308-L337

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower

theorem GlobalTheory.LOneLower.compare_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {α : ℝ}
    (hα : 0 < α) :
    ‖LFunction χ 1 * ((α⁻¹ : ℝ) : ℂ) - ∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ) : ℂ)‖ ≤ q := by sorry
