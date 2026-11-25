-- Prove2me | Theorems.Thm_GlobalTheory_T_hasSum_and_summable_on_ball_of_hasSum_on_interval
-- name    : GlobalTheory.T.hasSum_and_summable_on_ball_of_hasSum_on_interval
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:37.714844+00:00
-- url     : https://prove2.me/theorems/29c2a3be-59c8-56c8-933b-04f97e7d43f9
-- title:
--   T: has Sum and summable on ball of has Sum on interval
-- statement:
--   The T construction uses the has Sum and summable on ball of has Sum on interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GradedSeriesContinuationDominatedStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GradedSeriesContinuationDominatedStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GradedSeriesContinuationDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GradedSeriesContinuationDominatedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasSum_and_summable_on_ball_of_hasSum_on_interval : ∀ {ι : Type} (deg : ι → ℕ), (∀ k, {i | deg i = k}.Finite) → ∀ (a : ι → ℂ) (b : ι → ℝ) (C δ ρ : ℝ) (P P' : ℂ → ℂ), 0 < δ → (∀ i, 0 ≤ b i) → (∀ i, ‖a i‖ ≤ C * b i) → DifferentiableOn ℂ P (Metric.ball 0 ρ) → DifferentiableOn ℂ P' (Metric.ball 0 ρ) → (∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => a i * (x : ℂ) ^ deg i) (P x) ∧ HasSum (fun i => (b i : ℂ) * (x : ℂ) ^ deg i) (P' x)) → ∀ X : ℂ, ‖X‖ < ρ → HasSum (fun i => a i * X ^ deg i) (P X) ∧ Summable (fun i => b i * ‖X‖ ^ deg i) := by sorry
