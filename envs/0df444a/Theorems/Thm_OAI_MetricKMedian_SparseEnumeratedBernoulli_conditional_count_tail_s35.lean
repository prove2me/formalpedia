-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBernoulli_conditional_count_tail_s35
-- name    : OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:47:47.173013+00:00
-- url     : https://prove2.me/theorems/de555641-a4d4-44ee-a455-6357caa5beb6
-- title:
--   OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseEnumeratedBernoulli`, with `open Finset`):
--
--   ```lean
--   theorem conditional_count_tail_s35 (enum : Fin n ≃ E) (q a m : E → ℚ) (c : E → E → ℚ)
--       (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) {D p φ g A b : ℝ}
--       (hD : 1 ≤ D) (hp : 0 < p) (hφ : 0 < φ) (hg : 0 < g) (hb : 0 < b)
--       (hlarge : 1 < b*A) (hqP : ∀ i, (q i:ℝ) ≤ 2*p)
--       (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
--       (hsize : ∀ i, (a i:ℝ)+(m i:ℝ) ≤ b*A+2)
--       (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
--       (hrow : ∀ i, ∑ j, (c i j:ℝ) ≤ (D-1)*(m i:ℝ))
--       (hmass : (∑ i, (m i:ℝ)) ≤ 2*A/g)
--       (htotal : (∑ i, ((a i:ℝ)+(m i:ℝ))) ≤ 4*A/g)
--       (hsmall : 8*p*D ≤ φ*g)
--       (hlinear : (∑ i, ((a i:ℝ)-(m i:ℝ))*(q i:ℝ)) ≤ -p*φ*A) :
--       (law enum q hq).real.prob (fun ω => 0 <
--         CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) ω) ≤
--         96*D^2*b/(p*φ^2*g)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CountStatistic.statistic` and `OAI.MetricKMedian.FiniteLaw.prob` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.SparseEnumeratedBernoulli.law` (definitions bundle `OAIQ035K049` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K049

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedBernoulli
open Finset
variable {E : Type} [Fintype E] [DecidableEq E] {n : ℕ}

theorem conditional_count_tail_s35 (enum : Fin n ≃ E) (q a m : E → ℚ) (c : E → E → ℚ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) {D p φ g A b : ℝ}
    (hD : 1 ≤ D) (hp : 0 < p) (hφ : 0 < φ) (hg : 0 < g) (hb : 0 < b)
    (hlarge : 1 < b*A) (hqP : ∀ i, (q i:ℝ) ≤ 2*p)
    (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hsize : ∀ i, (a i:ℝ)+(m i:ℝ) ≤ b*A+2)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, (c i j:ℝ) ≤ (D-1)*(m i:ℝ))
    (hmass : (∑ i, (m i:ℝ)) ≤ 2*A/g)
    (htotal : (∑ i, ((a i:ℝ)+(m i:ℝ))) ≤ 4*A/g)
    (hsmall : 8*p*D ≤ φ*g)
    (hlinear : (∑ i, ((a i:ℝ)-(m i:ℝ))*(q i:ℝ)) ≤ -p*φ*A) :
    (law enum q hq).real.prob (fun ω => 0 <
      CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) ω) ≤
      96*D^2*b/(p*φ^2*g) := by
  sorry

end MetricKMedian.SparseEnumeratedBernoulli
end
end

end OAI
end
