-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_integralPrecision_spec_s238r
-- name    : OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision_spec_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:31:59.05125+00:00
-- url     : https://prove2.me/theorems/186587c7-7ee6-4f59-a983-5e1eb958c72c
-- title:
--   OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision_spec_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision_spec` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralPrecision.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralPrecision.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Sampling.Comparison`, with `open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling`):
--
--   ```lean
--   lemma integralPrecision_spec_s238r (D F S : Finset V) (hD : D.Nonempty) (hSF : S ⊆ F)
--       (Δ P : ℝ) (hΔ : 1 ≤ Δ) (m : ℕ)
--       (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f) :
--       Precise (blindUpdate D F S hD Δ P m) (mainActual D S Δ m)
--         (integralPrecision D Δ m) (2*m) (some State.initial)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Sampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.RadiusMenus.firstSize`, `OAI.MetricKMedianRecovery.RadiusMenus.geometricCap`, `OAI.MetricKMedianRecovery.RadiusMenus.thirdSize`, `OAI.MetricKMedianRecovery.Sampling.Action`, `OAI.MetricKMedianRecovery.Sampling.Entry`, `OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision`, `OAI.MetricKMedianRecovery.Sampling.Comparison.mainKappa` and `OAI.MetricKMedianRecovery.Sampling.Comparison.mainKappa_pos` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.Guided.FixedDyadic.Precise` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison.blindUpdate`, `OAI.MetricKMedianRecovery.Sampling.Comparison.mainActual` and `OAI.MetricKMedianRecovery.Sampling.State.initial` (definitions bundle `Q238L011` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralPrecision.lean (declaration OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision_spec)

import Mathlib
import Definitions.Def_Q238L011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable local instance instDecidableEqAction_2_r49f1a3_1 (D : Finset V) (M E J : ℕ) : DecidableEq (Action D M E J) := Classical.decEq _
lemma integralPrecision_spec_s238r (D F S : Finset V) (hD : D.Nonempty) (hSF : S ⊆ F)
    (Δ P : ℝ) (hΔ : 1 ≤ Δ) (m : ℕ)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f) :
    Precise (blindUpdate D F S hD Δ P m) (mainActual D S Δ m)
      (integralPrecision D Δ m) (2*m) (some State.initial) := by
  sorry

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end
