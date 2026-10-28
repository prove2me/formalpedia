-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_marginal_lower_s35
-- name    : OAI.MetricKMedian.SparseEnumeratedBatch.marginal_lower_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:43:11.995462+00:00
-- url     : https://prove2.me/theorems/6da8d4be-6990-491d-832e-8b48d5351e72
-- title:
--   OAI.MetricKMedian.SparseEnumeratedBatch.marginal_lower_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseEnumeratedBatch`, with `open Finset`):
--
--   ```lean
--   theorem marginal_lower_s35 (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
--       (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
--       {N : ℕ} (hq : ∀ e, (p:ℝ) ≤ q e) (hC : ∀ e, (C e).card ≤ N)
--       (hself : ∀ e, e ∉ C e) (e : E) :
--       (p:ℝ)/2-(N:ℝ)*(p:ℝ)^2/2 ≤ (law enum Z C p q hp hq0).real.prob (fun A => e ∈ A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw.prob` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.SparseEnumeratedBatch.law` (definitions bundle `OAIQ035K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseEnumeratedBatch.erasure_at_least_quarter_s35` of this split imports it.
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
namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem marginal_lower_s35 (enum : Fin n ≃ E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {N : ℕ} (hq : ∀ e, (p:ℝ) ≤ q e) (hC : ∀ e, (C e).card ≤ N)
    (hself : ∀ e, e ∉ C e) (e : E) :
    (p:ℝ)/2-(N:ℝ)*(p:ℝ)^2/2 ≤ (law enum Z C p q hp hq0).real.prob (fun A => e ∈ A) := by
  sorry

end MetricKMedian.SparseEnumeratedBatch
end
end

end OAI
end
