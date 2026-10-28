-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_prob_eq_s35
-- name    : OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:47:48.072978+00:00
-- url     : https://prove2.me/theorems/b90c89e4-b005-4ca8-8a36-4b1848e7a4c3
-- title:
--   OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseEnumeratedBatch`, with `open Finset`):
--
--   ```lean
--   theorem prob_eq_s35 (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
--       (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
--       (R : Finset E → Prop) [DecidablePred R] :
--       (law enum Z C p q hp hq).real.prob R=
--         (1/2)*(SparseEnumeratedBernoulli.law enum (fun _ => p) (fun _ => hp)).real.prob
--           (fun ω => R (PhysicalBatchLaw.balanced Z C ω))+
--         (1/2)*(SparseEnumeratedBernoulli.law enum q hq).real.prob
--           (fun ω => R (PhysicalBatchLaw.unbalanced Z ω))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw.prob` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.PhysicalBatchLaw.unbalanced` (definitions bundle `OAIQ035K011` of this split); `OAI.MetricKMedian.PhysicalBatchLaw.balanced` (definitions bundle `OAIQ035K024` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.SparseEnumeratedBatch.law` (definitions bundle `OAIQ035K039` of this split); `OAI.MetricKMedian.SparseEnumeratedBernoulli.law` (definitions bundle `OAIQ035K049` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseCopyState.physical_count_tail_s35` of this split imports it.
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
namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem prob_eq_s35 (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (R : Finset E → Prop) [DecidablePred R] :
    (law enum Z C p q hp hq).real.prob R=
      (1/2)*(SparseEnumeratedBernoulli.law enum (fun _ => p) (fun _ => hp)).real.prob
        (fun ω => R (PhysicalBatchLaw.balanced Z C ω))+
      (1/2)*(SparseEnumeratedBernoulli.law enum q hq).real.prob
        (fun ω => R (PhysicalBatchLaw.unbalanced Z ω)) := by
  sorry

end MetricKMedian.SparseEnumeratedBatch
end
end

end OAI
end
