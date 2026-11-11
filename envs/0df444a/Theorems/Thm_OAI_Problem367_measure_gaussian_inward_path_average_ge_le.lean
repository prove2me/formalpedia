-- Prove2me | Theorems.Thm_OAI_Problem367_measure_gaussian_inward_path_average_ge_le
-- name    : OAI.Problem367.measure_gaussian_inward_path_average_ge_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:21.980733+00:00
-- url     : https://prove2.me/theorems/df7eedc7-6ba7-49bd-8584-a9cae1283fe6
-- title:
--   OAI.Problem367.measure_gaussian_inward_path_average_ge_le: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.measure_gaussian_inward_path_average_ge_le` of [lean/OAI/Probability/FreeIsing/Gaussian/InwardCutConcentration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gaussian/InwardCutConcentration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal`, `open PathSideBranches InwardCutChannels CutContinuationChannels`):
--
--   ```lean
--   theorem measure_gaussian_inward_path_average_ge_le {d k : ℕ}
--       {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 2 ≤ d)
--       (t : ℝ≥0) (I : Finset (TreeShell d (k + 1))) (hI : I.Nonempty) (L : ℕ)
--       {τ : ℝ} (hτ : 0 ≤ τ)
--       (hmean : ∀ p ∈ I, (∫ z, inwardContinuationAverage μ t (Real.tanh beta) p L
--         (Finset.Ico (k + 1) (k + 1 + L)) z
--         ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤ τ / 4) :
--       (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
--         {z | Real.exp (4 * beta / (1 - Real.tanh beta)) * τ ≤
--           (∑ v ∈ cutDescendants I L,
--             rootPathProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) v.1) /
--               ((cutDescendants I L).card : ℝ)} ≤
--         ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.TreeShell` and `OAI.Problem367.cutDescendants` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.PlantedSymmetry.gaussianNoiseLaw` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.gaussianInwardConeFactor`, `OAI.Problem367.rootPathProduct` and `OAI.Problem367.InwardCutChannels.inwardContinuationAverage` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.measure_gaussian_inward_restricted_path_average_ge_le_double_exp` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gaussian/InwardCutConcentration.lean (declaration OAI.Problem367.measure_gaussian_inward_path_average_ge_le)

import Mathlib
import Mathlib.MeasureTheory.Function.FactorsThrough
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
open PathSideBranches InwardCutChannels CutContinuationChannels

theorem measure_gaussian_inward_path_average_ge_le {d k : ℕ}
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 2 ≤ d)
    (t : ℝ≥0) (I : Finset (TreeShell d (k + 1))) (hI : I.Nonempty) (L : ℕ)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hmean : ∀ p ∈ I, (∫ z, inwardContinuationAverage μ t (Real.tanh beta) p L
      (Finset.Ico (k + 1) (k + 1 + L)) z
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤ τ / 4) :
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
      {z | Real.exp (4 * beta / (1 - Real.tanh beta)) * τ ≤
        (∑ v ∈ cutDescendants I L,
          rootPathProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) v.1) /
            ((cutDescendants I L).card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2)) := by
  sorry

end Problem367

end

end OAI
end
