-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_history_menu_budget_s238
-- name    : OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:46:07.31621+00:00
-- url     : https://prove2.me/theorems/50c33fe2-fb32-43bd-bfcd-2234ceb3b6c8
-- title:
--   OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget` of [lean/OAI/Combinatorics/KMedianRecovery/Encoding/EntryIndex.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/EntryIndex.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Sampling.Comparison`, with `open RadiusMenus`, `open scoped Classical`):
--
--   ```lean
--   lemma history_menu_budget_s238 (C : Comparison D S O) (hD : D.Nonempty)
--       (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
--       (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
--       (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
--       (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
--         (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
--       (menuConstant mainKappa mainKappa_pos)^C.bad.card *
--         (2 : ℝ)^(-((10/(9*mainKappa)+1)*C.bad.card)) ≤
--           ∏ i : Fin n, actionMenuWeight C.bad.card (seed i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Sampling.State` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.RadiusMenus.firstSize`, `OAI.MetricKMedianRecovery.RadiusMenus.geometricCap`, `OAI.MetricKMedianRecovery.RadiusMenus.thirdSize`, `OAI.MetricKMedianRecovery.Sampling.Action`, `OAI.MetricKMedianRecovery.Sampling.Entry`, `OAI.MetricKMedianRecovery.Sampling.Comparison.mainKappa` and `OAI.MetricKMedianRecovery.Sampling.Comparison.mainKappa_pos` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.Guided.pathWeight`, `OAI.MetricKMedianRecovery.Sampling.Comparison`, `OAI.MetricKMedianRecovery.Sampling.comparisonCost` and `OAI.MetricKMedianRecovery.Guided.Kernel` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.RadiusMenus.menuConstant`, `OAI.MetricKMedianRecovery.Sampling.Comparison.bad` and `OAI.MetricKMedianRecovery.Sampling.State.initial` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.MainAction` and `OAI.MetricKMedianRecovery.Sampling.Comparison.actionMenuWeight` (definitions bundle `Q238K016` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.guideKernel` and `OAI.MetricKMedianRecovery.Sampling.Comparison.guidedUpdate` (definitions bundle `Q238K027` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/EntryIndex.lean (declaration OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget)

import Mathlib
import Definitions.Def_Q238K027

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

lemma history_menu_budget_s238 (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    (menuConstant mainKappa mainKappa_pos)^C.bad.card *
      (2 : ℝ)^(-((10/(9*mainKappa)+1)*C.bad.card)) ≤
        ∏ i : Fin n, actionMenuWeight C.bad.card (seed i) := by
  sorry

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end
