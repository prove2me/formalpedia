-- Prove2me | Theorems.Thm_GlobalTheory_LLeft_abel_three
-- name    : GlobalTheory.LLeft.abel_three
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:56.714244+00:00
-- url     : https://prove2.me/theorems/7547d4e6-c7c6-4861-9d47-bc7340d86ba8
-- title:
--   LLeft: abel three
-- statement:
--   The LLeft construction uses the abel three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L158-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L158-L183

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

theorem GlobalTheory.LLeft.abel_three (q : ℕ) (hq : 0 < q) (a : ℕ → ℂ) (hp : Function.Periodic a q)
    (h0 : ∑ n ∈ Finset.range q, a n = 0) (hM : ∀ n, ‖a n‖ ≤ 1) :
    ∃ (b : ℕ → ℂ) (μ₁ μ₂ μ₃ : ℂ), (∀ n, ‖b n‖ ≤ 8 * (q : ℝ) ^ 3) ∧ ‖μ₁‖ ≤ q ∧
      ‖μ₂‖ ≤ 2 * (q : ℝ) ^ 2 ∧ ‖μ₃‖ ≤ 4 * (q : ℝ) ^ 3 ∧
      ∀ s : ℂ, 1 < s.re → ∑' n : ℕ, a n * diffPow 0 s ((n : ℝ) + 1) =
        μ₁ * diffPow 0 s 1 + μ₂ * diffPow 1 s 1 + μ₃ * diffPow 2 s 1 +
          ∑' n : ℕ, b n * diffPow 3 s ((n : ℝ) + 1) := by sorry
