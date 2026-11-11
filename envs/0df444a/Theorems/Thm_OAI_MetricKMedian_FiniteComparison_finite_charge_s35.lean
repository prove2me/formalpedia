-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FiniteComparison_finite_charge_s35
-- name    : OAI.MetricKMedian.FiniteComparison.finite_charge_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:13:57.869994+00:00
-- url     : https://prove2.me/theorems/198cb885-7705-4aff-83ed-8cdf302e85a4
-- title:
--   OAI.MetricKMedian.FiniteComparison.finite_charge_s35: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.FiniteComparison.finite_charge` of [lean/OAI/Combinatorics/KMedian/Analysis/RowComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/RowComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FiniteComparison`):
--
--   ```lean
--   theorem finite_charge_s35 {I : Type*} [Fintype I] {π D R : I → ℝ}
--       {q : I → I → ℝ} {s : I → Bool} {p m a z h : ℝ} {b : Bool → ℝ}
--       (sb : ScalarBounds p m a z h b)
--       (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
--       (hD0 : ∀ i, 0 ≤ D i) (hD : average π D = 1)
--       (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
--       (hcomp : ∀ i t, q i t < 1 → R i * (1 - p * q i t) ≤ D i + D t) :
--       average π (fun i => rowValue π D (q i) p m a z b (s i) (D i) (R i)) ≤ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteComparison.average` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.FiniteComparison.rowValue` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.FiniteComparison.ScalarBounds` (definitions bundle `OAIQ035K029` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.GraphComparison.normalized_drift_le_s35` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/RowComparison.lean (declaration OAI.MetricKMedian.FiniteComparison.finite_charge)

import Mathlib
import Definitions.Def_OAIQ035K029

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FiniteComparison

theorem finite_charge_s35 {I : Type*} [Fintype I] {π D R : I → ℝ}
    {q : I → I → ℝ} {s : I → Bool} {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D = 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → R i * (1 - p * q i t) ≤ D i + D t) :
    average π (fun i => rowValue π D (q i) p m a z b (s i) (D i) (R i)) ≤ 0 := by
  sorry

end MetricKMedian.FiniteComparison

end
end

end OAI
end
