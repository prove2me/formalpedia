-- Prove2me | Theorems.Thm_GlobalTheory_gradedSeries_continuation_dominated
-- name    : GlobalTheory.gradedSeries_continuation_dominated
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:11.164805+00:00
-- url     : https://prove2.me/theorems/e32d3481-aa91-4ac0-8f1a-1da58a9eb44a
-- title:
--   Global Theory: graded Series continuation dominated
-- statement:
--   The Global Theory construction uses the graded Series continuation dominated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GradedSeriesContinuationDominated.lean#L84-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GradedSeriesContinuationDominated.lean#L84-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GradedSeriesContinuationDominated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Metric Set
open GlobalTheory

theorem GlobalTheory.gradedSeries_continuation_dominated : ∀ {ι : Type} (deg : ι → ℕ),
    (∀ k, {i | deg i = k}.Finite) → ∀ (a : ι → ℂ) (b : ι → ℝ) (C δ ρ : ℝ) (P P' : ℂ → ℂ),
    0 < δ → (∀ i, 0 ≤ b i) → (∀ i, ‖a i‖ ≤ C * b i) →
    DifferentiableOn ℂ P (Metric.ball 0 ρ) → DifferentiableOn ℂ P' (Metric.ball 0 ρ) →
    (∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => a i * (x : ℂ) ^ deg i) (P x) ∧
      HasSum (fun i => (b i : ℂ) * (x : ℂ) ^ deg i) (P' x)) →
    ∀ X : ℂ, ‖X‖ < ρ → HasSum (fun i => a i * X ^ deg i) (P X) ∧
      Summable (fun i => b i * ‖X‖ ^ deg i) := by sorry
