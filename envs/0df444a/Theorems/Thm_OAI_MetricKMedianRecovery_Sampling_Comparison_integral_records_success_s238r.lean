-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_integral_records_success_s238r
-- name    : OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:36:43.238938+00:00
-- url     : https://prove2.me/theorems/85e39016-5635-4292-b9c1-b57f3a9b639b
-- title:
--   OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralPrecision.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralPrecision.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Sampling.Comparison`, with `open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling Precision`):
--
--   ```lean
--   theorem integral_records_success_s238r {D S O : Finset V}
--       (C : Comparison D S O) (hD : D.Nonempty)
--       (F : Finset V) (hOF : O ⊆ F) (hSF : S ⊆ F) (Δ : ℝ) (hΔ : 1 ≤ Δ)
--       (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f)
--       (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
--       (1/2:ℝ)^(2*C.bad.card) * samplingBound C.bad.card ≤
--         probability (fun bits => Hits
--           (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
--           (C.stop hD Δ) (2*C.bad.card) (some State.initial)
--           (integralActions D F S hD Δ (comparisonCost D C.assign) C.bad.card bits))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.FiniteSampling.probability` and `OAI.MetricKMedianRecovery.Sampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.RadiusMenus.firstSize`, `OAI.MetricKMedianRecovery.RadiusMenus.geometricCap`, `OAI.MetricKMedianRecovery.RadiusMenus.thirdSize`, `OAI.MetricKMedianRecovery.Sampling.Action`, `OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision`, `OAI.MetricKMedianRecovery.Sampling.Comparison.mainKappa` and `OAI.MetricKMedianRecovery.Sampling.Comparison.mainKappa_pos` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.Guided.Hits`, `OAI.MetricKMedianRecovery.Sampling.Comparison` and `OAI.MetricKMedianRecovery.Sampling.comparisonCost` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.IntegralBits`, `OAI.MetricKMedianRecovery.Sampling.Comparison.bad`, `OAI.MetricKMedianRecovery.Sampling.Comparison.blindUpdate`, `OAI.MetricKMedianRecovery.Sampling.Comparison.stop` and `OAI.MetricKMedianRecovery.Sampling.State.initial` (definitions bundle `Q238L011` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.integralActions` and `OAI.MetricKMedianRecovery.Sampling.Comparison.samplingBound` (definitions bundle `Q238L021` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralPrecision.lean (declaration OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success)

import Mathlib
import Definitions.Def_Q238L021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling Precision
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

attribute [local instance] OAI.MetricKMedianRecovery.Sampling.Comparison.instDecidableEqAction_2
theorem integral_records_success_s238r {D S O : Finset V}
    (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (hSF : S ⊆ F) (Δ : ℝ) (hΔ : 1 ≤ Δ)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    (1/2:ℝ)^(2*C.bad.card) * samplingBound C.bad.card ≤
      probability (fun bits => Hits
        (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
        (C.stop hD Δ) (2*C.bad.card) (some State.initial)
        (integralActions D F S hD Δ (comparisonCost D C.assign) C.bad.card bits)) := by
  sorry

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end
