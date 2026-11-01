-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseBernoulli_count_variance_s53
-- name    : OAI.MetricKMedian.SparseBernoulli.count_variance_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:43:06.354446+00:00
-- url     : https://prove2.me/theorems/422a9759-a480-47a2-8698-b6558c1ab7a4
-- title:
--   OAI.MetricKMedian.SparseBernoulli.count_variance_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.SparseBernoulli.count_variance` of [lean/OAI/Combinatorics/KMedian/Sparse/SparseCountStatistic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseCountStatistic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseBernoulli`, with `open Finset`):
--
--   ```lean
--   theorem count_variance_s53 (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
--       (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) :
--       (run (d := 4) p hp n).real.variance
--           (CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ)))=
--         (reference p hp).variance
--           (CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CountStatistic.statistic` (definitions bundle `OAIQ053K006` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.FiniteLaw.variance` (definitions bundle `OAIQ053K018` of this split); `OAI.MetricKMedian.SparseBernoulli.reference` (definitions bundle `OAIQ053K037` of this split); `OAI.MetricKMedian.SparseBernoulli.run` (definitions bundle `OAIQ053K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseBernoulli.conditional_count_tail_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseCountStatistic.lean (declaration OAI.MetricKMedian.SparseBernoulli.count_variance)

import Mathlib
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K039

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

theorem count_variance_s53 (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) :
    (run (d := 4) p hp n).real.variance
        (CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ)))=
      (reference p hp).variance
        (CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ))) := by
  sorry

end MetricKMedian.SparseBernoulli
end
end

end OAI
end
