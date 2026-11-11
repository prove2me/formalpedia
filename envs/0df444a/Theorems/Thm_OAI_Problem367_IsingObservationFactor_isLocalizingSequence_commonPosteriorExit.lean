-- Prove2me | Theorems.Thm_OAI_Problem367_IsingObservationFactor_isLocalizingSequence_commonPosteriorExit
-- name    : OAI.Problem367.IsingObservationFactor.isLocalizingSequence_commonPosteriorExit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:47:44.75563+00:00
-- url     : https://prove2.me/theorems/954f23d6-62e3-47b2-84d1-06c97e9d239d
-- title:
--   OAI.Problem367.IsingObservationFactor.isLocalizingSequence_commonPosteriorExit: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingObservationFactor.isLocalizingSequence_commonPosteriorExit` of [lean/OAI/Probability/FreeIsing/Ising/CanonicalPosteriorStops.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CanonicalPosteriorStops.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingObservationFactor`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal Topology`, `open IsingObservationInnovation IsingCopyEnergy PosteriorCompensatorStopping`):
--
--   ```lean
--    theorem isLocalizingSequence_commonPosteriorExit
--       {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       [IsProbabilityMeasure μ]
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
--       IsLocalizingSequence ContinuousCopyBrownian.joinedFiltration.rightCont
--         (commonPosteriorExit beta v) (copies beta μ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ContinuousCopyBrownian.Joint`, `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.ContinuousCopyBrownian.joinedFiltration` (definitions bundle `Q243FI003` of this split); `OAI.Problem367.IsingObservationFactor.commonPosteriorExit` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.IsingObservationFactor.actual_variance_analysis_of_common_local_square` and `OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CanonicalPosteriorStops.lean (declaration OAI.Problem367.IsingObservationFactor.isLocalizingSequence_commonPosteriorExit)

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section

attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy PosteriorCompensatorStopping

 theorem isLocalizingSequence_commonPosteriorExit
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    IsLocalizingSequence ContinuousCopyBrownian.joinedFiltration.rightCont
      (commonPosteriorExit beta v) (copies beta μ) := by
  sorry

end Problem367.IsingObservationFactor

end

end OAI
end
