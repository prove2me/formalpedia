-- Prove2me | Theorems.Thm_GlobalTheory_LLeft_abel_step
-- name    : GlobalTheory.LLeft.abel_step
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:41.443368+00:00
-- url     : https://prove2.me/theorems/0facd7ee-c4c4-4e50-8ccb-19fe1d96d6b3
-- title:
--   LLeft: abel step
-- statement:
--   The LLeft construction uses the abel step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L83-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L83-L147

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

theorem GlobalTheory.LLeft.abel_step (q : ℕ) (hq : 0 < q) (a : ℕ → ℂ) (M : ℝ) (hp : Function.Periodic a q)
    (h0 : ∑ n ∈ Finset.range q, a n = 0) (hM : ∀ n, ‖a n‖ ≤ M) :
    ∃ (b : ℕ → ℂ) (μ : ℂ), Function.Periodic b q ∧ ∑ n ∈ Finset.range q, b n = 0 ∧
      (∀ n, ‖b n‖ ≤ 2 * q * M) ∧ ‖μ‖ ≤ q * M ∧
      ∀ f : ℕ → ℂ, Summable (fun n => ‖f n‖) →
        ∑' n, a n * f n = μ * f 0 + ∑' n, b n * (f n - f (n + 1)) := by sorry
