-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_pair_le
-- name    : OAI.MetricKMedian.SparseEnumeratedBatch.pair_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:32:00.411994+00:00
-- url     : https://prove2.me/theorems/7a5c4a49-0c43-474d-966b-48ee1b6d6798
-- title:
--   OAI.MetricKMedian.SparseEnumeratedBatch.pair_le: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseEnumeratedBatch`, with `open Finset`):
--
--   ```lean
--   theorem pair_le (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
--       (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
--       (e f : E) (hef : e≠f) :
--       (law enum Z C p q hp hq).real.prob (fun A => e∈A ∧ f∈A) ≤
--         ((p:ℝ)^2+(q e:ℝ)*(q f:ℝ))/2
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw.prob` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.SparseEnumeratedBatch.law` (definitions bundle `OAIQ035K039` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.SparseEnumeratedBatch.erasure_at_least_quarter` and `OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate` of this split import it.
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

namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem pair_le (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (e f : E) (hef : e≠f) :
    (law enum Z C p q hp hq).real.prob (fun A => e∈A ∧ f∈A) ≤
      ((p:ℝ)^2+(q e:ℝ)*(q f:ℝ))/2 := by
  sorry

end MetricKMedian.SparseEnumeratedBatch

end OAI
end
