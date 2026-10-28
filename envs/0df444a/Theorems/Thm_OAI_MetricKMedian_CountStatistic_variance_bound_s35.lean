-- Prove2me | Theorems.Thm_OAI_MetricKMedian_CountStatistic_variance_bound_s35
-- name    : OAI.MetricKMedian.CountStatistic.variance_bound_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:34:07.206606+00:00
-- url     : https://prove2.me/theorems/d3453472-4a51-4234-96da-fc4d76470b19
-- title:
--   OAI.MetricKMedian.CountStatistic.variance_bound_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.CountStatistic`, with `open Finset`):
--
--   ```lean
--   theorem variance_bound_s35 (p a m : I → ℝ) (c : I → I → ℝ)
--       (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
--       {D P B : ℝ} (hD : 1 ≤ D) (hP : 0 ≤ P)
--       (hpP : ∀ i, p i ≤ P) (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
--       (hsize : ∀ i, a i+m i ≤ B)
--       (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
--       (hrow : ∀ i, ∑ j, c i j ≤ (D-1)*m i) :
--       (FiniteLaw.bernoulli p hp0 hp1).variance (statistic (fun i => a i-m i) c) ≤
--         P*D^2*B*(∑ i : I, (a i+m i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CountStatistic.statistic`, `OAI.MetricKMedian.FiniteLaw.bernoulli` and `OAI.MetricKMedian.FiniteLaw.variance` (definitions bundle `OAIQ035K004` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseBernoulli.count_failure_s35` of this split imports it.
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
namespace MetricKMedian.CountStatistic

open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem variance_bound_s35 (p a m : I → ℝ) (c : I → I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {D P B : ℝ} (hD : 1 ≤ D) (hP : 0 ≤ P)
    (hpP : ∀ i, p i ≤ P) (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hsize : ∀ i, a i+m i ≤ B)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, c i j ≤ (D-1)*m i) :
    (FiniteLaw.bernoulli p hp0 hp1).variance (statistic (fun i => a i-m i) c) ≤
      P*D^2*B*(∑ i : I, (a i+m i)) := by
  sorry

end MetricKMedian.CountStatistic
end
end

end OAI
end
