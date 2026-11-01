-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_erasure_lower_s53
-- name    : OAI.MetricKMedian.SparseEnumeratedBatch.erasure_lower_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:43:29.820717+00:00
-- url     : https://prove2.me/theorems/a563800d-ab34-4e9f-9d47-1cafe2a0ca46
-- title:
--   OAI.MetricKMedian.SparseEnumeratedBatch.erasure_lower_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.SparseEnumeratedBatch.erasure_lower` of [lean/OAI/Combinatorics/KMedian/Sparse/SparseEnumeratedSurvival.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseEnumeratedSurvival.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseEnumeratedBatch`, with `open Finset`):
--
--   ```lean
--   theorem erasure_lower_s53 (enum : Fin n ≃ E) (Z R : Finset E) (C : E → Finset E)
--       (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
--       (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
--       {N : ℕ} (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ 2*(p:ℝ)) (hC : ∀ e, (C e).card ≤ N)
--       (hself : ∀ e, e ∉ C e) :
--       (R.card:ℝ)*(p:ℝ)/2-(R.card:ℝ)*(N:ℝ)*(p:ℝ)^2/2-2*(R.card:ℝ)^2*(p:ℝ)^2 ≤
--         (law enum Z C p q hp hq0).real.prob (fun A => ∃ e ∈ R, e ∈ A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.FiniteLaw.prob` (definitions bundle `OAIQ053K018` of this split); `OAI.MetricKMedian.SparseEnumeratedBatch.law` (definitions bundle `OAIQ053K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalBatchData.proposal_survival_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseEnumeratedSurvival.lean (declaration OAI.MetricKMedian.SparseEnumeratedBatch.erasure_lower)

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
namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem erasure_lower_s53 (enum : Fin n ≃ E) (Z R : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {N : ℕ} (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ 2*(p:ℝ)) (hC : ∀ e, (C e).card ≤ N)
    (hself : ∀ e, e ∉ C e) :
    (R.card:ℝ)*(p:ℝ)/2-(R.card:ℝ)*(N:ℝ)*(p:ℝ)^2/2-2*(R.card:ℝ)^2*(p:ℝ)^2 ≤
      (law enum Z C p q hp hq0).real.prob (fun A => ∃ e ∈ R, e ∈ A) := by
  sorry

end MetricKMedian.SparseEnumeratedBatch
end
end

end OAI
end
