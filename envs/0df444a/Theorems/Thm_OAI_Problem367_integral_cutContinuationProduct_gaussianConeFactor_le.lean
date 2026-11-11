-- Prove2me | Theorems.Thm_OAI_Problem367_integral_cutContinuationProduct_gaussianConeFactor_le
-- name    : OAI.Problem367.integral_cutContinuationProduct_gaussianConeFactor_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:25.172736+00:00
-- url     : https://prove2.me/theorems/5610bd35-cabb-40fa-919c-f8c905f1b47e
-- title:
--   OAI.Problem367.integral_cutContinuationProduct_gaussianConeFactor_le: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.integral_cutContinuationProduct_gaussianConeFactor_le` of [lean/OAI/Probability/FreeIsing/Gaussian/CutChannels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gaussian/CutChannels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal`, `open PathSideBranches CutContinuationChannels`):
--
--   ```lean
--   theorem integral_cutContinuationProduct_gaussianConeFactor_le {d k L : ℕ}
--       {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
--       (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
--       {t : ℝ≥0} (ht : 0 < t)
--       (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
--       (∫ z, cutContinuationProduct (gaussianConeFactor μ t (Real.tanh beta) z) p w
--         ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
--           Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
--             min (Real.sqrt (t : ℝ)) 1) * (L : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ReducedTail`, `OAI.Problem367.TreeShell`, `OAI.Problem367.cutContinuationProduct` and `OAI.Problem367.cutLastColor` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.ComponentSignalAttenuation.lossCoefficient` and `OAI.Problem367.PlantedSymmetry.gaussianNoiseLaw` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.gaussianConeFactor` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.IsingOrientedPath.measure_extensionAverage_gt_le_double_exp_common` and `OAI.Problem367.IsingRootDoubleExponential.integral_root_weight_mul_sq_le_double_exp` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gaussian/CutChannels.lean (declaration OAI.Problem367.integral_cutContinuationProduct_gaussianConeFactor_le)

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
open PathSideBranches CutContinuationChannels

theorem integral_cutContinuationProduct_gaussianConeFactor_le {d k L : ℕ}
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
    (∫ z, cutContinuationProduct (gaussianConeFactor μ t (Real.tanh beta) z) p w
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
        Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
          min (Real.sqrt (t : ℝ)) 1) * (L : ℝ)) := by
  sorry

end Problem367

end

end OAI
end
