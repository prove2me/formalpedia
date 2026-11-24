-- Prove2me | Theorems.Thm_GlobalTheory_LOneLower_char_sum_bound
-- name    : GlobalTheory.LOneLower.char_sum_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:04.459801+00:00
-- url     : https://prove2.me/theorems/88732e8a-18fc-4543-9ed7-5b10514b8f75
-- title:
--   LOne Lower: char sum bound
-- statement:
--   The LOne Lower construction uses the char sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L42-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L42-L74

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

theorem GlobalTheory.LOneLower.char_sum_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q)‖ ≤ q := by sorry
