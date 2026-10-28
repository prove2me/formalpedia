-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseBernoulli_count_failure
-- name    : OAI.MetricKMedian.SparseBernoulli.count_failure
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-27T08:30:41.444238+00:00
-- url     : https://prove2.me/theorems/422f874c-58b9-4eff-8b7a-788092cd177f
-- title:
--   OAI.MetricKMedian.SparseBernoulli.count_failure: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseBernoulli`, with `open Finset`):
--
--   ```lean
--   theorem count_failure (p a m : Fin n → ℚ) (c : Fin n → Fin n → ℚ)
--       (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
--       {D P B t : ℝ} (hD : 1 ≤ D) (hP : 0 ≤ P) (ht : 0 < t)
--       (hpP : ∀ i, (p i:ℝ) ≤ P) (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
--       (hsize : ∀ i, (a i:ℝ)+(m i:ℝ) ≤ B)
--       (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
--       (hrow : ∀ i, ∑ j, (c i j:ℝ) ≤ (D-1)*(m i:ℝ))
--       (hlinear : (∑ i, ((a i:ℝ)-(m i:ℝ))*(p i:ℝ)) ≤
--         -t-(1/2)*P^2*(D-1)*∑ i, (m i:ℝ)) :
--       (run (d := 4) p hp n).real.prob (fun q => 0 <
--         CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) q) ≤
--         (P*D^2*B*(∑ i, ((a i:ℝ)+(m i:ℝ))))/t^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CountStatistic.statistic` and `OAI.MetricKMedian.FiniteLaw.prob` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.SparseBernoulli.run` (definitions bundle `OAIQ035K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K039

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

theorem count_failure (p a m : Fin n → ℚ) (c : Fin n → Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {D P B t : ℝ} (hD : 1 ≤ D) (hP : 0 ≤ P) (ht : 0 < t)
    (hpP : ∀ i, (p i:ℝ) ≤ P) (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hsize : ∀ i, (a i:ℝ)+(m i:ℝ) ≤ B)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, (c i j:ℝ) ≤ (D-1)*(m i:ℝ))
    (hlinear : (∑ i, ((a i:ℝ)-(m i:ℝ))*(p i:ℝ)) ≤
      -t-(1/2)*P^2*(D-1)*∑ i, (m i:ℝ)) :
    (run (d := 4) p hp n).real.prob (fun q => 0 <
      CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) q) ≤
      (P*D^2*B*(∑ i, ((a i:ℝ)+(m i:ℝ))))/t^2 := by
  sorry

end MetricKMedian.SparseBernoulli
end
end

end OAI
end
