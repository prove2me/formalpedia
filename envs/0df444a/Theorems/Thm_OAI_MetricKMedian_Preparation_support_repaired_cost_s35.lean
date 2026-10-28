-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_support_repaired_cost_s35
-- name    : OAI.MetricKMedian.Preparation.support_repaired_cost_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:34:52.345798+00:00
-- url     : https://prove2.me/theorems/7d31b1dd-2ed3-4f31-b32d-e4e65082a239
-- title:
--   OAI.MetricKMedian.Preparation.support_repaired_cost_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation`, with `open Finset`):
--
--   ```lean
--   theorem support_repaired_cost_s35 (μ : FiniteLaw Ω) (ball : Finset I)
--       (y a : Ω → I → ℝ) (d : I → ℝ) {R H V : ℝ}
--       (hR : 0 ≤ R) (ha : ∀ ω, 0 < μ.weight ω → ∀ i, 0 ≤ a ω i)
--       (hay : ∀ ω, 0 < μ.weight ω → ∀ i, a ω i ≤ y ω i)
--       (hd : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ ball, d i ≤ R)
--       (hball : ∀ ω, 0 < μ.weight ω → 1 ≤ ∑ i ∈ ball, y ω i)
--       (hcost : μ.expect (fun ω => ∑ i, a ω i*d i) ≤ V)
--       (hshort : μ.expect (fun ω => max (1-∑ i, a ω i) 0) ≤ H) :
--       ∃ r : Ω → I → ℝ,
--         (∀ ω, 0 < μ.weight ω → (∀ i, 0 ≤ r ω i ∧ r ω i ≤ y ω i) ∧ (∑ i, r ω i)=1) ∧
--         μ.expect (fun ω => ∑ i, r ω i*d i) ≤ V+R*H
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw` and `OAI.MetricKMedian.FiniteLaw.expect` (definitions bundle `OAIQ035K004` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Preparation.nearby_assignments_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]

theorem support_repaired_cost_s35 (μ : FiniteLaw Ω) (ball : Finset I)
    (y a : Ω → I → ℝ) (d : I → ℝ) {R H V : ℝ}
    (hR : 0 ≤ R) (ha : ∀ ω, 0 < μ.weight ω → ∀ i, 0 ≤ a ω i)
    (hay : ∀ ω, 0 < μ.weight ω → ∀ i, a ω i ≤ y ω i)
    (hd : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ ball, d i ≤ R)
    (hball : ∀ ω, 0 < μ.weight ω → 1 ≤ ∑ i ∈ ball, y ω i)
    (hcost : μ.expect (fun ω => ∑ i, a ω i*d i) ≤ V)
    (hshort : μ.expect (fun ω => max (1-∑ i, a ω i) 0) ≤ H) :
    ∃ r : Ω → I → ℝ,
      (∀ ω, 0 < μ.weight ω → (∀ i, 0 ≤ r ω i ∧ r ω i ≤ y ω i) ∧ (∑ i, r ω i)=1) ∧
      μ.expect (fun ω => ∑ i, r ω i*d i) ≤ V+R*H := by
  sorry

end MetricKMedian.Preparation
end
end

end OAI
end
