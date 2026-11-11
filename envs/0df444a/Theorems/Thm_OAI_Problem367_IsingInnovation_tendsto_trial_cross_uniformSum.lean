-- Prove2me | Theorems.Thm_OAI_Problem367_IsingInnovation_tendsto_trial_cross_uniformSum
-- name    : OAI.Problem367.IsingInnovation.tendsto_trial_cross_uniformSum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:43:44.258832+00:00
-- url     : https://prove2.me/theorems/ba351f5d-a7c1-454f-8b67-fcd2a8ce9fc3
-- title:
--   OAI.Problem367.IsingInnovation.tendsto_trial_cross_uniformSum: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingInnovation.tendsto_trial_cross_uniformSum` of [lean/OAI/Probability/FreeIsing/Ising/MixedFiltering.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/MixedFiltering.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingInnovation`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`):
--
--   ```lean
--   theorem tendsto_trial_cross_uniformSum
--       {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
--       (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
--       (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
--       (v u : TreeVertex d) {H : ℝ≥0 → State d A → ℝ} {L : ℝ}
--       (hH : StronglyAdapted (ArrayPosteriorStationarity.filtration B hmB) H)
--       (hcH : ∀ q, Continuous (fun t => H t q))
--       (hL : 0 ≤ L) (hbH : ∀ t q, |H t q| ≤ L) (T : ℝ≥0) :
--       Tendsto (fun n : ℕ => ∫ q, posterior beta B v T q *
--         BrownianGrid.uniformSum (innovation beta B u) H T n q
--           ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) atTop
--         (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ q,
--           H r.toNNReal q * covariance beta B v u r.toNNReal q
--             ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingInnovation.State`, `OAI.Problem367.IsingInnovation.innovation` and `OAI.Problem367.IsingInnovation.posterior` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.BrownianGrid.uniformSum` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.ArrayPosteriorStationarity.filtration` (definitions bundle `Q243FI003` of this split); `OAI.Problem367.IsingInnovation.covariance` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingInnovation.exists_posterior_integral_representation` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/MixedFiltering.lean (declaration OAI.Problem367.IsingInnovation.tendsto_trial_cross_uniformSum)

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI003
import Definitions.Def_Q243FI004

section

attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem tendsto_trial_cross_uniformSum
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) {H : ℝ≥0 → State d A → ℝ} {L : ℝ}
    (hH : StronglyAdapted (ArrayPosteriorStationarity.filtration B hmB) H)
    (hcH : ∀ q, Continuous (fun t => H t q))
    (hL : 0 ≤ L) (hbH : ∀ t q, |H t q| ≤ L) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ q, posterior beta B v T q *
      BrownianGrid.uniformSum (innovation beta B u) H T n q
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) atTop
      (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ q,
        H r.toNNReal q * covariance beta B v u r.toNNReal q
          ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))) := by
  sorry

end Problem367.IsingInnovation

end

end OAI
end
