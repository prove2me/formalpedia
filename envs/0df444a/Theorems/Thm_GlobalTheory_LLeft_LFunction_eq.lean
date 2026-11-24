-- Prove2me | Theorems.Thm_GlobalTheory_LLeft_LFunction_eq
-- name    : GlobalTheory.LLeft.LFunction_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:40.1438+00:00
-- url     : https://prove2.me/theorems/52b699db-c533-40d3-b49a-f148357f4636
-- title:
--   LLeft: LFunction eq
-- statement:
--   The LLeft construction uses the LFunction eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L205-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L205-L263

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open GlobalTheory.LLeft

theorem GlobalTheory.LLeft.LFunction_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ (b : ℕ → ℂ) (μ₁ μ₂ μ₃ : ℂ), (∀ n, ‖b n‖ ≤ 8 * (q : ℝ) ^ 3) ∧ ‖μ₁‖ ≤ q ∧
      ‖μ₂‖ ≤ 2 * (q : ℝ) ^ 2 ∧ ‖μ₃‖ ≤ 4 * (q : ℝ) ^ 3 ∧
      ∀ s : ℂ, -(15 / 8 : ℝ) < s.re → LFunction χ s =
        μ₁ * diffPow 0 s 1 + μ₂ * diffPow 1 s 1 + μ₃ * diffPow 2 s 1 +
          ∑' n : ℕ, b n * diffPow 3 s ((n : ℝ) + 1) := by sorry
