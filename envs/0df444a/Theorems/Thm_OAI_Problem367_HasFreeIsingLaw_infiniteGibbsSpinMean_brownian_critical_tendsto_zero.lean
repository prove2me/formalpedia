-- Prove2me | Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_infiniteGibbsSpinMean_brownian_critical_tendsto_zero
-- name    : OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_tendsto_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:47.506418+00:00
-- url     : https://prove2.me/theorems/641b26b5-58b4-4e5f-9971-eb2f392908df
-- title:
--   OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_tendsto_zero: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_tendsto_zero` of [lean/OAI/Probability/FreeIsing/Gibbs/CovarianceCriticalEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gibbs/CovarianceCriticalEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal Topology BigOperators`, `open PlantedSymmetry`):
--
--   ```lean
--   theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_tendsto_zero
--       {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
--       {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
--       (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
--       (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
--       (hmB : ∀ i t, Measurable (B i t)) (v : TreeVertex d) :
--       Tendsto (fun t : ℝ≥0 => ∫ p, infiniteGibbsSpinMean beta v
--         (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
--         ∂μ.prod (Measure.infinitePi ν)) (𝓝 0) (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.infiniteGibbsSpinMean` and `OAI.Problem367.spinSign` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gibbs/CovarianceCriticalEnergy.lean (declaration OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_tendsto_zero)

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI000

section

attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators
namespace Problem367
open PlantedSymmetry

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_tendsto_zero
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (v : TreeVertex d) :
    Tendsto (fun t : ℝ≥0 => ∫ p, infiniteGibbsSpinMean beta v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) (𝓝 0) (𝓝 0) := by
  sorry

end Problem367

end

end OAI
end
