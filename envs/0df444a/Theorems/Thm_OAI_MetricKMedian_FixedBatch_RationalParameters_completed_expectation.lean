-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FixedBatch_RationalParameters_completed_expectation
-- name    : OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-27T08:34:16.468143+00:00
-- url     : https://prove2.me/theorems/5d110e81-993a-40d1-a788-c95e7d0482f2
-- title:
--   OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FixedBatch.RationalParameters`, with `open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational`):
--
--   ```lean
--   theorem completed_expectation (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
--       (location : F → X) (client : Fin j → X)
--       (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
--       (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
--       (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
--       (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty)
--       (hA : 1 ≤ mass (q.g:ℝ) A) (hBA : ∀ c, B c ⊆ A)
--       (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (q.g:ℝ) (B c)=1)
--       (hdR : ∀ c i, i∈B c → d c i.1 ≤ R c) (hatt : ∀ c, ∃ i∈B c, R c=d c i.1) :
--       (q.tree d₀ A).expectation (fun z => (score d (completed d R B hB q.g q.β z):ℝ)) ≤
--         (1+2/Real.exp 1+τ)*(∑ c, PhysicalPotential.cost (q.g:ℝ)
--           (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Completion.Rational.score` (definitions bundle `OAIQ035K002` of this split); `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.SparseHistories.History` (definitions bundle `OAIQ035K005` of this split); `OAI.MetricKMedian.PhysicalPotential.cost` (definitions bundle `OAIQ035K007` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.State` (definitions bundle `OAIQ035K017` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.completed` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.SparseIntegerLaw.expectation` (definitions bundle `OAIQ035K045` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters.tree` (definitions bundle `OAIQ035K047` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K047

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}

theorem completed_expectation (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty)
    (hA : 1 ≤ mass (q.g:ℝ) A) (hBA : ∀ c, B c ⊆ A)
    (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (q.g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1 ≤ R c) (hatt : ∀ c, ∃ i∈B c, R c=d c i.1) :
    (q.tree d₀ A).expectation (fun z => (score d (completed d R B hB q.g q.β z):ℝ)) ≤
      (1+2/Real.exp 1+τ)*(∑ c, PhysicalPotential.cost (q.g:ℝ)
        (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c)) := by
  sorry

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end
