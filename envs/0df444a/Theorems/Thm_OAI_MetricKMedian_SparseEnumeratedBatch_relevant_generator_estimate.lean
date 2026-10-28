-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_relevant_generator_estimate
-- name    : OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:32:22.252328+00:00
-- url     : https://prove2.me/theorems/abdbf8bc-6185-4400-83bb-38eb423c357d
-- title:
--   OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseEnumeratedBatch`, with `open Finset`):
--
--   ```lean
--   theorem relevant_generator_estimate (enum : Fin n ≃ E) (Z R : Finset E) (C : E → Finset E)
--       (p : ℚ) (q : E → ℚ) (b : E → ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
--       (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
--       {φ K Q : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
--       (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q)
--       (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
--       (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
--       (D : Finset E → ℝ)
--       (hb : ∀ e ∈ R, |b e| ≤ K) (hD : ∀ A, D A ≤ K)
--       (hzero : ∀ A, A ∩ R=∅ → D A ≤ 0)
--       (hone : ∀ A e, A ∩ R={e} → D A ≤ b e) :
--       (law enum Z C p q hp hq0).real.expect D ≤
--         ((p:ℝ)/2)*(∑ e ∈ R, b e)+(R.card:ℝ)*K*((N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2)+
--           2*K*((univ : Finset R).offDiag.card:ℝ)*Q^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw.expect` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.SparseEnumeratedBatch.law` (definitions bundle `OAIQ035K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound` of this split imports it.
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

theorem relevant_generator_estimate (enum : Fin n ≃ E) (Z R : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (b : E → ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {φ K Q : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    (D : Finset E → ℝ)
    (hb : ∀ e ∈ R, |b e| ≤ K) (hD : ∀ A, D A ≤ K)
    (hzero : ∀ A, A ∩ R=∅ → D A ≤ 0)
    (hone : ∀ A e, A ∩ R={e} → D A ≤ b e) :
    (law enum Z C p q hp hq0).real.expect D ≤
      ((p:ℝ)/2)*(∑ e ∈ R, b e)+(R.card:ℝ)*K*((N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2)+
        2*K*((univ : Finset R).offDiag.card:ℝ)*Q^2 := by
  sorry

end MetricKMedian.SparseEnumeratedBatch

end OAI
end
