-- Prove2me | Theorems.Thm_OAI_Problem367_IsingObservationFactor_canonicalCovarianceEnergy_integrable
-- name    : OAI.Problem367.IsingObservationFactor.canonicalCovarianceEnergy_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:46:15.150058+00:00
-- url     : https://prove2.me/theorems/7161af4b-3b5e-4d95-960a-95d7860b8d3e
-- title:
--   OAI.Problem367.IsingObservationFactor.canonicalCovarianceEnergy_integrable: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingObservationFactor.canonicalCovarianceEnergy_integrable` of [lean/OAI/Probability/FreeIsing/Ising/CanonicalArtanh.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CanonicalArtanh.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingObservationFactor`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal Topology`, `open IsingObservationInnovation PosteriorCompensatorStopping ArtanhMartingaleFormula`):
--
--   ```lean
--    theorem canonicalCovarianceEnergy_integrable
--       {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) (T : ℝ≥0) :
--       Integrable (fun p : ℝ × Paths d => canonicalCovarianceEnergy beta v p.1.toNNReal p.2)
--         ((volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.IsingObservationInnovation.observationLaw`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.IsingObservationFactor.canonicalCovarianceEnergy` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.IsingObservationFactor.canonicalPosteriorExit_localizing` and `OAI.Problem367.IsingObservationFactor.canonical_artanh_decomposition` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CanonicalArtanh.lean (declaration OAI.Problem367.IsingObservationFactor.canonicalCovarianceEnergy_integrable)

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
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
open IsingObservationInnovation PosteriorCompensatorStopping ArtanhMartingaleFormula

 theorem canonicalCovarianceEnergy_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Paths d => canonicalCovarianceEnergy beta v p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) := by
  sorry

end Problem367.IsingObservationFactor

end

end OAI
end
