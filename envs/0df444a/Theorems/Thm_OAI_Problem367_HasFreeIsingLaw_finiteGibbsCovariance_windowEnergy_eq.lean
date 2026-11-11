-- Prove2me | Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_finiteGibbsCovariance_windowEnergy_eq
-- name    : OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovariance_windowEnergy_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:41:41.462402+00:00
-- url     : https://prove2.me/theorems/ec5e4ccf-c187-4b0f-9b8a-71d260d5d6d5
-- title:
--   OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovariance_windowEnergy_eq: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovariance_windowEnergy_eq` of [lean/OAI/Probability/FreeIsing/Gibbs/CovarianceWindowEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gibbs/CovarianceWindowEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal Topology BigOperators`, `open PlantedSymmetry GaussianTreeCovariance`):
--
--   ```lean
--   theorem HasFreeIsingLaw.finiteGibbsCovariance_windowEnergy_eq
--       {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
--       {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
--       (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
--       (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
--       (hmB : ∀ i t, Measurable (B i t))
--       (hcB : ∀ i omega, Continuous (fun t => B i t omega))
--       (v : TreeVertex d) (n : ℕ) {δ T : ℝ} (hδ : 0 ≤ δ) (hδT : δ ≤ T) :
--       (∑' w, ∫ p, finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2
--         ∂(volume.restrict (Ioc δ T)).prod (μ.prod (Measure.infinitePi ν))) =
--       (∫ p, finiteGibbsSpinMean beta v n (brownianIsingObservationR B (T, p)) ^ 2
--         ∂μ.prod (Measure.infinitePi ν)) -
--       ∫ p, finiteGibbsSpinMean beta v n (brownianIsingObservationR B (δ, p)) ^ 2
--         ∂μ.prod (Measure.infinitePi ν)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.finiteGibbsSpinMean` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.brownianIsingObservationR` and `OAI.Problem367.finiteGibbsCovariance` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_windowEnergy_eq` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gibbs/CovarianceWindowEnergy.lean (declaration OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovariance_windowEnergy_eq)

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI004

section

attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators
namespace Problem367
open PlantedSymmetry GaussianTreeCovariance

theorem HasFreeIsingLaw.finiteGibbsCovariance_windowEnergy_eq
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) (n : ℕ) {δ T : ℝ} (hδ : 0 ≤ δ) (hδT : δ ≤ T) :
    (∑' w, ∫ p, finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2
      ∂(volume.restrict (Ioc δ T)).prod (μ.prod (Measure.infinitePi ν))) =
    (∫ p, finiteGibbsSpinMean beta v n (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) -
    ∫ p, finiteGibbsSpinMean beta v n (brownianIsingObservationR B (δ, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν) := by
  sorry

end Problem367

end

end OAI
end
