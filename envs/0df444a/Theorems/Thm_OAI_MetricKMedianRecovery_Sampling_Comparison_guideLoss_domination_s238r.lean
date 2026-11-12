-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_guideLoss_domination_s238r
-- name    : OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:41:04.580644+00:00
-- url     : https://prove2.me/theorems/5cd148fd-3334-4007-a426-32c8c314a5f9
-- title:
--   OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Guide.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Guide.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Sampling.Comparison`, with `open RadiusMenus`, `open scoped Classical`):
--
--   ```lean
--   lemma guideLoss_domination_s238r (C : Comparison D S O) (hD : D.Nonempty)
--       (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
--       (s : Option (State V)) (a : MainAction D C.bad.card) :
--       C.guideLoss hD Δ s a * (C.guideKernel hD Δ hΔ hP hm).weight s a ≤
--         (C.stoppedActual hD Δ).weight s a
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Sampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.RadiusMenus.firstSize`, `OAI.MetricKMedianRecovery.RadiusMenus.geometricCap`, `OAI.MetricKMedianRecovery.RadiusMenus.thirdSize`, `OAI.MetricKMedianRecovery.Sampling.Action`, `OAI.MetricKMedianRecovery.Sampling.Entry`, `OAI.MetricKMedianRecovery.Sampling.Comparison.mainKappa` and `OAI.MetricKMedianRecovery.Sampling.Comparison.mainKappa_pos` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison`, `OAI.MetricKMedianRecovery.Sampling.comparisonCost` and `OAI.MetricKMedianRecovery.Guided.Kernel` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.MainAction` and `OAI.MetricKMedianRecovery.Sampling.Comparison.bad` (definitions bundle `Q238L011` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.stoppedActual` (definitions bundle `Q238L021` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.guideKernel` and `OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss` (definitions bundle `Q238L026` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Guide.lean (declaration OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination)

import Mathlib
import Definitions.Def_Q238L021
import Definitions.Def_Q238L026

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus
open scoped Classical

lemma guideLoss_domination_s238r (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : Option (State V)) (a : MainAction D C.bad.card) :
    C.guideLoss hD Δ s a * (C.guideKernel hD Δ hΔ hP hm).weight s a ≤
      (C.stoppedActual hD Δ).weight s a := by
  sorry

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end
