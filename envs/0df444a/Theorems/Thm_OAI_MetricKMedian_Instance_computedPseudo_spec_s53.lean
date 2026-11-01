-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Instance_computedPseudo_spec_s53
-- name    : OAI.MetricKMedian.Instance.computedPseudo_spec_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:45:50.525994+00:00
-- url     : https://prove2.me/theorems/435f5b7b-c478-4152-ac2c-bc891d4f3b48
-- title:
--   OAI.MetricKMedian.Instance.computedPseudo_spec_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Instance.computedPseudo_spec` of [lean/OAI/Combinatorics/KMedian/Programs/InstanceComputedPseudo.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Programs/InstanceComputedPseudo.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Instance`, with `open Finset Preparation`):
--
--   ```lean
--    theorem computedPseudo_spec_s53 (I : Instance) (r : ℕ) (hr : 0 < r)
--       {η τ : ℝ} (p : RationalAllParameters η τ) (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
--       (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
--       I.computedPseudo r hr p C⊆I.facilities ∧ (I.computedPseudo r hr p C).Nonempty ∧
--         (I.computedPseudo r hr p C).card≤I.k+C ∧
--         cost I (I.computedPseudo r hr p C)≤
--           (((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(1+3/(r:ℝ)))*optimum I
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FixedBatch.RationalParameters.allowance` and `OAI.MetricKMedian.FixedBatch.RationalParameters` (definitions bundle `OAIQ053K015` of this split); `OAI.MetricKMedian.Preparation.RationalAllParameters` (definitions bundle `OAIQ053K030` of this split); `OAI.MetricKMedian.Instance.computedPseudo` (definitions bundle `OAIQ053K058` of this split); `OAI.MetricKMedian.Instance`, `OAI.MetricKMedian.cost` and `OAI.MetricKMedian.optimum` (the published bundle `Def_KMedianThreshold`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.factor_above_threshold_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Programs/InstanceComputedPseudo.lean (declaration OAI.MetricKMedian.Instance.computedPseudo_spec)

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K058

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.Instance
open Finset Preparation

 theorem computedPseudo_spec_s53 (I : Instance) (r : ℕ) (hr : 0 < r)
    {η τ : ℝ} (p : RationalAllParameters η τ) (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
    (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
    I.computedPseudo r hr p C⊆I.facilities ∧ (I.computedPseudo r hr p C).Nonempty ∧
      (I.computedPseudo r hr p C).card≤I.k+C ∧
      cost I (I.computedPseudo r hr p C)≤
        (((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(1+3/(r:ℝ)))*optimum I := by
  sorry

end MetricKMedian.Instance
end

end OAI
end
