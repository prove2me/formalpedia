-- Prove2me | Theorems.Thm_OAI_MetricKMedian_WeightedRounding_exact_law_s35
-- name    : OAI.MetricKMedian.WeightedRounding.exact_law_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:34:59.598252+00:00
-- url     : https://prove2.me/theorems/4e8dbc0d-e73e-4cd4-9f90-691f838d19a6
-- title:
--   OAI.MetricKMedian.WeightedRounding.exact_law_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.WeightedRounding`, with `open Finset`):
--
--   ```lean
--   theorem exact_law_s35 (p : I → ℝ) (K : ℕ) (hp0 : ∀ i, 0 ≤ p i)
--       (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i=K) :
--       ∃ μ : FiniteLaw (Finset I),
--         (∀ S, 0 < μ.weight S → S.card=K) ∧
--         (∀ i, μ.prob (fun S => i ∈ S)=p i) ∧
--         (∀ i j, i ≠ j → μ.expect (fun S => indicator S i*indicator S j) ≤ p i*p j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw`, `OAI.MetricKMedian.FiniteLaw.expect` and `OAI.MetricKMedian.FiniteLaw.prob` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.WeightedRounding.indicator` (definitions bundle `OAIQ035K012` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding
open Finset
variable {I : Type} [Fintype I] [DecidableEq I]

theorem exact_law_s35 (p : I → ℝ) (K : ℕ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i=K) :
    ∃ μ : FiniteLaw (Finset I),
      (∀ S, 0 < μ.weight S → S.card=K) ∧
      (∀ i, μ.prob (fun S => i ∈ S)=p i) ∧
      (∀ i j, i ≠ j → μ.expect (fun S => indicator S i*indicator S j) ≤ p i*p j) := by
  sorry

end MetricKMedian.WeightedRounding
end
end

end OAI
end
