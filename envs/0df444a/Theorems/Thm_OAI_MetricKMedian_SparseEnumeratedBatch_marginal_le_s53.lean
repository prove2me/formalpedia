-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_marginal_le_s53
-- name    : OAI.MetricKMedian.SparseEnumeratedBatch.marginal_le_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:43:48.645544+00:00
-- url     : https://prove2.me/theorems/98a1e26c-8d4e-4431-987c-b59273258441
-- title:
--   OAI.MetricKMedian.SparseEnumeratedBatch.marginal_le_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_le` of [lean/OAI/Combinatorics/KMedian/Sparse/SparseEnumeratedBatch.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseEnumeratedBatch.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseEnumeratedBatch`, with `open Finset`):
--
--   ```lean
--   theorem marginal_le_s53 (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
--       (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
--       {Q : ℝ} (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q) (e : E) :
--       (law enum Z C p q hp hq).real.prob (fun A => e∈A) ≤ Q/2
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.FiniteLaw.prob` (definitions bundle `OAIQ053K018` of this split); `OAI.MetricKMedian.SparseEnumeratedBatch.law` (definitions bundle `OAIQ053K039` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s53` and `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound_s53` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseEnumeratedBatch.lean (declaration OAI.MetricKMedian.SparseEnumeratedBatch.marginal_le)

import Mathlib
import Definitions.Def_OAIQ053K039

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem marginal_le_s53 (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {Q : ℝ} (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q) (e : E) :
    (law enum Z C p q hp hq).real.prob (fun A => e∈A) ≤ Q/2 := by
  sorry

end MetricKMedian.SparseEnumeratedBatch

end OAI
end
