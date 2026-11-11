-- Prove2me | Theorems.Thm_OAI_Problem367_IsingCopyEnergy_copy_row_energy_integrable
-- name    : OAI.Problem367.IsingCopyEnergy.copy_row_energy_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:41:40.54012+00:00
-- url     : https://prove2.me/theorems/064226ec-60a4-411c-85c6-9fec48b051c0
-- title:
--   OAI.Problem367.IsingCopyEnergy.copy_row_energy_integrable: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingCopyEnergy.copy_row_energy_integrable` of [lean/OAI/Probability/FreeIsing/Ising/CopyEnergyIntegrability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopyEnergyIntegrability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingCopyEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal ENNReal Topology`, `open IsingObservationInnovation IsingObservationFactor`):
--
--   ```lean
--   theorem copy_row_energy_integrable
--       {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       [IsProbabilityMeasure μ]
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (v : TreeVertex d) (j : Bool) {T : ℝ} (hT : 0 ≤ T) :
--       (∀ᵐ p ∂(volume.restrict (Ioc 0 T)).prod (copies beta μ),
--         Summable (fun w => responseRow beta v w (timeProjection j p) ^ 2)) ∧
--       Integrable (fun p => ∑' w, responseRow beta v w (timeProjection j p) ^ 2)
--         ((volume.restrict (Ioc 0 T)).prod (copies beta μ)) ∧
--       (∫ p, ∑' w, responseRow beta v w (timeProjection j p) ^ 2
--         ∂(volume.restrict (Ioc 0 T)).prod (copies beta μ)) ≤
--         2 * ((d : ℝ) * beta + T + Real.sqrt T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingCopyEnergy.Joint`, `OAI.Problem367.IsingCopyEnergy.responseRow`, `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.IsingCopyEnergy.timeProjection` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.IsingContinuousCopyCoefficients.response_row_energy`, `OAI.Problem367.IsingObservationFactor.actual_variance_analysis_of_common_local_square`, `OAI.Problem367.IsingObservationFactor.isLocalizingSequence_commonPosteriorExit` and `OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopyEnergyIntegrability.lean (declaration OAI.Problem367.IsingCopyEnergy.copy_row_energy_integrable)

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI004

section

attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.IsingCopyEnergy
open IsingObservationInnovation IsingObservationFactor

theorem copy_row_energy_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (j : Bool) {T : ℝ} (hT : 0 ≤ T) :
    (∀ᵐ p ∂(volume.restrict (Ioc 0 T)).prod (copies beta μ),
      Summable (fun w => responseRow beta v w (timeProjection j p) ^ 2)) ∧
    Integrable (fun p => ∑' w, responseRow beta v w (timeProjection j p) ^ 2)
      ((volume.restrict (Ioc 0 T)).prod (copies beta μ)) ∧
    (∫ p, ∑' w, responseRow beta v w (timeProjection j p) ^ 2
      ∂(volume.restrict (Ioc 0 T)).prod (copies beta μ)) ≤
      2 * ((d : ℝ) * beta + T + Real.sqrt T) := by
  sorry

end Problem367.IsingCopyEnergy

end

end OAI
end
