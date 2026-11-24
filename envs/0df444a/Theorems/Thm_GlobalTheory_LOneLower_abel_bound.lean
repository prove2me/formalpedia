-- Prove2me | Theorems.Thm_GlobalTheory_LOneLower_abel_bound
-- name    : GlobalTheory.LOneLower.abel_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:04.764798+00:00
-- url     : https://prove2.me/theorems/eb67e94c-73f7-43b4-b60a-85860ca433da
-- title:
--   LOne Lower: abel bound
-- statement:
--   The LOne Lower construction uses the abel bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L8-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L8-L40

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

theorem GlobalTheory.LOneLower.abel_bound (a : ℕ → ℂ) (b : ℕ → ℝ) (M : ℝ) (hA : ∀ N, ‖∑ n ∈ Finset.range N, a n‖ ≤ M)
    (hb : Antitone b) (hb0 : ∀ n, 0 ≤ b n) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, a n * (b n : ℂ)‖ ≤ M * b 0 := by sorry
