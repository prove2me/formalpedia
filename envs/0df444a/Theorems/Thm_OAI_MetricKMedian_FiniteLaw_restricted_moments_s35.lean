-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FiniteLaw_restricted_moments_s35
-- name    : OAI.MetricKMedian.FiniteLaw.restricted_moments_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:34:30.180897+00:00
-- url     : https://prove2.me/theorems/83c11abb-fc9c-490d-8d48-d410889a7d81
-- title:
--   OAI.MetricKMedian.FiniteLaw.restricted_moments_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FiniteLaw`, with `open Finset`):
--
--   ```lean
--   theorem restricted_moments_s35 (μ : FiniteLaw Ω) (Y : Ω → I → ℝ) (q : I → ℝ)
--       (A : Finset I) {g : ℝ} (hm : ∀ i, μ.expect (fun ω => Y ω i)=q i)
--       (hv : ∀ i, μ.variance (fun ω => Y ω i) ≤ g*q i)
--       (hp : ∀ i j, i ≠ j → μ.expect (fun ω => Y ω i*Y ω j) ≤ q i*q j) :
--       μ.expect (fun ω => ∑ i ∈ A, Y ω i)=(∑ i ∈ A, q i) ∧
--       μ.variance (fun ω => ∑ i ∈ A, Y ω i) ≤ g*(∑ i ∈ A, q i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw`, `OAI.MetricKMedian.FiniteLaw.expect` and `OAI.MetricKMedian.FiniteLaw.variance` (definitions bundle `OAIQ035K004` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.Preparation.bundle_subset_moments_s35` and `OAI.MetricKMedian.Preparation.shortfall_from_deviation_s35` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

theorem restricted_moments_s35 (μ : FiniteLaw Ω) (Y : Ω → I → ℝ) (q : I → ℝ)
    (A : Finset I) {g : ℝ} (hm : ∀ i, μ.expect (fun ω => Y ω i)=q i)
    (hv : ∀ i, μ.variance (fun ω => Y ω i) ≤ g*q i)
    (hp : ∀ i j, i ≠ j → μ.expect (fun ω => Y ω i*Y ω j) ≤ q i*q j) :
    μ.expect (fun ω => ∑ i ∈ A, Y ω i)=(∑ i ∈ A, q i) ∧
    μ.variance (fun ω => ∑ i ∈ A, Y ω i) ≤ g*(∑ i ∈ A, q i) := by
  sorry

end MetricKMedian.FiniteLaw
end
end

end OAI
end
