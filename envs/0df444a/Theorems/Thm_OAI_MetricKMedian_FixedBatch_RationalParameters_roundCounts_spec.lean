-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FixedBatch_RationalParameters_roundCounts_spec
-- name    : OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:33:52.612798+00:00
-- url     : https://prove2.me/theorems/7b86010a-5201-4882-a625-9ee1e42732ef
-- title:
--   OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FixedBatch.RationalParameters`, with `open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational`, `open Preparation.RationalNearest`):
--
--   ```lean
--   theorem roundCounts_spec (hτ : τ<1) (hj : 0<j)
--       (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
--       (location : F → X) (client : Fin j → X)
--       (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
--       (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
--       (n : F → ℕ) (hn : ∀ a, n a ≤ q.Δ) (hm : 1 ≤ ∑ a, (q.g:ℝ)*(n a:ℝ))
--       (r : Fin j → F → ℝ) (hr0 : ∀ c a, 0 ≤ r c a)
--       (hr1 : ∀ c a, r c a ≤ (q.g:ℝ)*(n a:ℝ)) (hrsum : ∀ c, ∑ a, r c a=1) :
--       ∃ O : Finset F, q.roundCounts d₀ d n=some O ∧ O.Nonempty ∧
--         (O.card:ℝ) ≤ (∑ a, (q.g:ℝ)*(n a:ℝ))+(q.allowance:ℝ) ∧
--         (score d O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(∑ c,∑ a, r c a*(d c a:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Completion.Rational.score` (definitions bundle `OAIQ035K002` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters.allowance` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts` (definitions bundle `OAIQ035K047` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_certificate` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
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
open Preparation.RationalNearest
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {j : ℕ}

variable [Fintype F]

theorem roundCounts_spec (hτ : τ<1) (hj : 0<j)
    (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (n : F → ℕ) (hn : ∀ a, n a ≤ q.Δ) (hm : 1 ≤ ∑ a, (q.g:ℝ)*(n a:ℝ))
    (r : Fin j → F → ℝ) (hr0 : ∀ c a, 0 ≤ r c a)
    (hr1 : ∀ c a, r c a ≤ (q.g:ℝ)*(n a:ℝ)) (hrsum : ∀ c, ∑ a, r c a=1) :
    ∃ O : Finset F, q.roundCounts d₀ d n=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (∑ a, (q.g:ℝ)*(n a:ℝ))+(q.allowance:ℝ) ∧
      (score d O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(∑ c,∑ a, r c a*(d c a:ℝ)) := by
  sorry

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end
