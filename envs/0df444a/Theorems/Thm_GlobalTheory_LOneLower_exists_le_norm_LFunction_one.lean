-- Prove2me | Theorems.Thm_GlobalTheory_LOneLower_exists_le_norm_LFunction_one
-- name    : GlobalTheory.LOneLower.exists_le_norm_LFunction_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:55:49.137137+00:00
-- url     : https://prove2.me/theorems/3bd751fb-9261-413d-a344-a425a7c99cf8
-- title:
--   LOne Lower: exists le norm LFunction one
-- statement:
--   The LOne Lower construction uses the exists le norm LFunction one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L354-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L354-L361

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

theorem GlobalTheory.LOneLower.exists_le_norm_LFunction_one : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      c / (q : ℝ) ^ ((3 : ℝ) / 2) ≤ ‖LFunction χ 1‖ := by sorry
