-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_valid_execution_bounded_price_strictness_s238
-- name    : OAI.MetricKMedianRecovery.valid_execution_bounded_price_strictness_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:25:24.023496+00:00
-- url     : https://prove2.me/theorems/c689bd48-debb-4547-bcb5-3cbd8fc84eda
-- title:
--   OAI.MetricKMedianRecovery.valid_execution_bounded_price_strictness_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.valid_execution_bounded_price_strictness` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/RemovalReplay.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RemovalReplay.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery`):
--
--   ```lean
--   theorem valid_execution_bounded_price_strictness_s238
--       {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
--       {steps q : ℕ} (v lam eta T : ℝ)
--       (E : ValidExecution D X steps v lam eta) (cluster : Fin q ↪ D) (i : X)
--       (hq : 0 < q) (hi : i ∈ E.regular)
--       (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam) (hT : 0 < T)
--       (hP : 0 < ∑ j, dist i (E.location (cluster j)))
--       (hprice : lam ≤ T * ∑ j, dist i (E.location (cluster j)))
--       (hsmall : v ^ 2 ≤ ((1 / (200 * (T + 2))) ^ 2 / 100) / (6 * (T + 2))) :
--       (∑ j, (E.state steps).budget (cluster j)) ≤
--         lam + (2 - ((1 / (200 * (T + 2))) ^ 2 / 100) / 2) *
--           ∑ j, dist i (E.location (cluster j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.ExecutionState` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.ValidExecution` (definitions bundle `Q238K016` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RemovalReplay.lean (declaration OAI.MetricKMedianRecovery.valid_execution_bounded_price_strictness)

import Mathlib
import Definitions.Def_Q238K016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

theorem valid_execution_bounded_price_strictness_s238
    {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    {steps q : ℕ} (v lam eta T : ℝ)
    (E : ValidExecution D X steps v lam eta) (cluster : Fin q ↪ D) (i : X)
    (hq : 0 < q) (hi : i ∈ E.regular)
    (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam) (hT : 0 < T)
    (hP : 0 < ∑ j, dist i (E.location (cluster j)))
    (hprice : lam ≤ T * ∑ j, dist i (E.location (cluster j)))
    (hsmall : v ^ 2 ≤ ((1 / (200 * (T + 2))) ^ 2 / 100) / (6 * (T + 2))) :
    (∑ j, (E.state steps).budget (cluster j)) ≤
      lam + (2 - ((1 / (200 * (T + 2))) ^ 2 / 100) / 2) *
        ∑ j, dist i (E.location (cluster j)) := by
  sorry

end MetricKMedianRecovery

end OAI
end
