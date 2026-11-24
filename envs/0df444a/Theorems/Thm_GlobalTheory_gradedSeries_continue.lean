-- Prove2me | Theorems.Thm_GlobalTheory_gradedSeries_continue
-- name    : GlobalTheory.gradedSeries_continue
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:19.765164+00:00
-- url     : https://prove2.me/theorems/08f5ad66-39c9-46f2-9602-a69d1270771e
-- title:
--   Global Theory: graded Series continue
-- statement:
--   The Global Theory construction uses the graded Series continue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GradedSeriesContinuationDominated.lean#L22-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GradedSeriesContinuationDominated.lean#L22-L82

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

theorem GlobalTheory.gradedSeries_continue {ι : Type} (deg : ι → ℕ) (c : ι → ℂ) (δ ρ : ℝ) (Q : ℂ → ℂ)
    (hδ : 0 < δ) (hQ : DifferentiableOn ℂ Q (ball 0 ρ))
    (h : ∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => c i * (x : ℂ) ^ deg i) (Q x))
    (X : ℂ) (hX : ‖X‖ < ρ) :
    HasSum (fun k => (∑' i : deg ⁻¹' {k}, c i) * X ^ k) (Q X) := by sorry
