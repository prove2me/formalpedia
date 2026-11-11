-- Prove2me | Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_gaussian_root_information_le_component
-- name    : OAI.Problem367.HasFreeIsingLaw.gaussian_root_information_le_component
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:00.189468+00:00
-- url     : https://prove2.me/theorems/6cf4c145-810a-4da2-8093-302b0c2a5685
-- title:
--   OAI.Problem367.HasFreeIsingLaw.gaussian_root_information_le_component: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.HasFreeIsingLaw.gaussian_root_information_le_component` of [lean/OAI/Probability/FreeIsing/Gaussian/SiteInformation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gaussian/SiteInformation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal`):
--
--   ```lean
--   theorem HasFreeIsingLaw.gaussian_root_information_le_component
--       {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (t : ℝ≥0) (c : Fin d) :
--       (∫ z, (PlantedSymmetry.posteriorMagnetization
--         (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) t
--         (RootedBroadcast.root d) z) ^ 2
--         ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
--         (1 + (Real.tanh beta) ^ 2) * gaussianComponentInformation μ t c
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.RootedBroadcast.root` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.PlantedSymmetry.gaussianNoiseLaw` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.gaussianComponentInformation` and `OAI.Problem367.PlantedSymmetry.posteriorMagnetization` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_tendsto_zero` and `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_zero` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gaussian/SiteInformation.lean (declaration OAI.Problem367.HasFreeIsingLaw.gaussian_root_information_le_component)

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI004

section

attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem HasFreeIsingLaw.gaussian_root_information_le_component
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    (∫ z, (PlantedSymmetry.posteriorMagnetization
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) t
      (RootedBroadcast.root d) z) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      (1 + (Real.tanh beta) ^ 2) * gaussianComponentInformation μ t c := by
  sorry

end Problem367

end

end OAI
end
