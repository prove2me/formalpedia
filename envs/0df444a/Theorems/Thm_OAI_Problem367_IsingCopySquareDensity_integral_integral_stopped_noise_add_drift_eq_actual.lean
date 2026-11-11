-- Prove2me | Theorems.Thm_OAI_Problem367_IsingCopySquareDensity_integral_integral_stopped_noise_add_drift_eq_actual
-- name    : OAI.Problem367.IsingCopySquareDensity.integral_integral_stopped_noise_add_drift_eq_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:45:44.438809+00:00
-- url     : https://prove2.me/theorems/e4bace0f-385d-4408-85c5-21759d3f52b4
-- title:
--   OAI.Problem367.IsingCopySquareDensity.integral_integral_stopped_noise_add_drift_eq_actual: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingCopySquareDensity.integral_integral_stopped_noise_add_drift_eq_actual` of [lean/OAI/Probability/FreeIsing/Ising/CopySquareDensity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopySquareDensity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingCopySquareDensity`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal`, `open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy`, `open IsingContinuousCopyDensity StoppedTimePrimitive`):
--
--   ```lean
--   theorem integral_integral_stopped_noise_add_drift_eq_actual
--       (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       (τ : Joint d → WithTop ℝ≥0) (T : ℝ≥0) :
--       (∫ s in (0 : ℝ)..(T : ℝ), ∫ q,
--         stopDensity (noise hb) τ s.toNNReal q +
--           2 * stoppedProcess (continuousDifference beta (ConnectedHull.root d)) τ s.toNNReal q *
--             stopDensity (drift beta) τ s.toNNReal q ∂copies beta μ) =
--         ∫ s in (0 : ℝ)..(T : ℝ), ∫ q,
--           if (s.toNNReal : WithTop ℝ≥0) ≤ τ q then
--             IsingCopyEnergy.density beta (ConnectedHull.root d) s q else 0
--             ∂copies beta μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ConnectedHull.root`, `OAI.Problem367.IsingCopyEnergy.Joint`, `OAI.Problem367.IsingCopyEnergy.density`, `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.StoppedTimePrimitive.stopDensity` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.IsingCopySquareDensity.drift`, `OAI.Problem367.IsingCopySquareDensity.noise` and `OAI.Problem367.IsingObservationFactor.continuousDifference` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopySquareDensity.lean (declaration OAI.Problem367.IsingCopySquareDensity.integral_integral_stopped_noise_add_drift_eq_actual)

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySquareDensity
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy
open IsingContinuousCopyDensity StoppedTimePrimitive

variable {d : ℕ} {beta : ℝ}

theorem integral_integral_stopped_noise_add_drift_eq_actual
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (τ : Joint d → WithTop ℝ≥0) (T : ℝ≥0) :
    (∫ s in (0 : ℝ)..(T : ℝ), ∫ q,
      stopDensity (noise hb) τ s.toNNReal q +
        2 * stoppedProcess (continuousDifference beta (ConnectedHull.root d)) τ s.toNNReal q *
          stopDensity (drift beta) τ s.toNNReal q ∂copies beta μ) =
      ∫ s in (0 : ℝ)..(T : ℝ), ∫ q,
        if (s.toNNReal : WithTop ℝ≥0) ≤ τ q then
          IsingCopyEnergy.density beta (ConnectedHull.root d) s q else 0
          ∂copies beta μ := by
  sorry

end Problem367.IsingCopySquareDensity

end

end OAI
end
