-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseBernoulli_conditional_count_tail_s53
-- name    : OAI.MetricKMedian.SparseBernoulli.conditional_count_tail_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:42:44.909612+00:00
-- url     : https://prove2.me/theorems/5c54a9d9-fb1e-4dbc-97c1-5331fb669c04
-- title:
--   OAI.MetricKMedian.SparseBernoulli.conditional_count_tail_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.SparseBernoulli.conditional_count_tail` of [lean/OAI/Combinatorics/KMedian/Sparse/SparseConditionalCount.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseConditionalCount.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseBernoulli`, with `open Finset`):
--
--   ```lean
--   theorem conditional_count_tail_s53 (q a m : Fin n → ℚ) (c : Fin n → Fin n → ℚ)
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
--       (run (d := 4) q hq n).real.prob (fun ω => 0 <
--         CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) ω) ≤
--         96*D^2*b/(p*φ^2*g)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CountStatistic.statistic` (definitions bundle `OAIQ053K006` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.FiniteLaw.prob` (definitions bundle `OAIQ053K018` of this split); `OAI.MetricKMedian.SparseBernoulli.run` (definitions bundle `OAIQ053K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseConditionalCount.lean (declaration OAI.MetricKMedian.SparseBernoulli.conditional_count_tail)

import Mathlib
import Definitions.Def_OAIQ053K039

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
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

theorem conditional_count_tail_s53 (q a m : Fin n → ℚ) (c : Fin n → Fin n → ℚ)
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
    (run (d := 4) q hq n).real.prob (fun ω => 0 <
      CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) ω) ≤
      96*D^2*b/(p*φ^2*g) := by
  sorry

end MetricKMedian.SparseBernoulli
end
end

end OAI
end
