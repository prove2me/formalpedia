-- Prove2me | Theorems.Thm_GlobalTheory_LOneLower_compare_right
-- name    : GlobalTheory.LOneLower.compare_right
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:15.423034+00:00
-- url     : https://prove2.me/theorems/efd85f89-c671-4d3c-977f-5791ea5d44a5
-- title:
--   LOne Lower: compare right
-- statement:
--   The LOne Lower construction uses the compare right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L256-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L256-L306

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

theorem GlobalTheory.LOneLower.compare_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {α ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε) :
    ‖LFunction χ (1 + ε) * ((α⁻¹ : ℝ) : ℂ) - ∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ)‖ ≤ q := by sorry
