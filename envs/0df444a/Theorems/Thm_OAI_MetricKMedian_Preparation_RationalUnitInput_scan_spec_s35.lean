-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_RationalUnitInput_scan_spec_s35
-- name    : OAI.MetricKMedian.Preparation.RationalUnitInput.scan_spec_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:48:34.306373+00:00
-- url     : https://prove2.me/theorems/a0093938-b2ee-4836-870d-785f0fe34ceb
-- title:
--   OAI.MetricKMedian.Preparation.RationalUnitInput.scan_spec_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation.RationalUnitInput`, with `open Finset`):
--
--   ```lean
--   theorem scan_spec_s35 (hτ0 : 0<τ) (hτ : τ<1) (hj : 0<j) (B : ℚ)
--       (hB : (∑ a, (U.y a:ℝ))+3*(p.round.g:ℝ)+(p.round.allowance:ℝ) ≤ (B:ℝ)) :
--       ∃ O : Finset (Fin f), U.scan R p B=some O ∧ O.Nonempty ∧ (O.card:ℝ)≤(B:ℝ) ∧
--         (Completion.Rational.score U.dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(∑ c, (U.V c:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Completion.Rational.score` (definitions bundle `OAIQ035K002` of this split); `OAI.MetricKMedian.Preparation.RationalUnitInput` and `OAI.MetricKMedian.Preparation.RationalUnitInput.Realization` (definitions bundle `OAIQ035K009` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.Preparation.RationalUnitInput.V` (definitions bundle `OAIQ035K023` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters.allowance` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.Preparation.RationalAllParameters` (definitions bundle `OAIQ035K033` of this split); `OAI.MetricKMedian.Preparation.RationalUnitInput.scan` (definitions bundle `OAIQ035K062` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Preparation.FractionalRefinement.scan_spec_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K062

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.Preparation.RationalUnitInput
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (U : RationalUnitInput f j) (R : U.Realization X) {η τ : ℝ} (p : RationalAllParameters η τ)

theorem scan_spec_s35 (hτ0 : 0<τ) (hτ : τ<1) (hj : 0<j) (B : ℚ)
    (hB : (∑ a, (U.y a:ℝ))+3*(p.round.g:ℝ)+(p.round.allowance:ℝ) ≤ (B:ℝ)) :
    ∃ O : Finset (Fin f), U.scan R p B=some O ∧ O.Nonempty ∧ (O.card:ℝ)≤(B:ℝ) ∧
      (Completion.Rational.score U.dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(∑ c, (U.V c:ℝ)) := by
  sorry

end MetricKMedian.Preparation.RationalUnitInput
end

end OAI
end
