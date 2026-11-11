-- Prove2me | Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_infiniteGibbsCovariance_timeEnergy_eq
-- name    : OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:41:49.862299+00:00
-- url     : https://prove2.me/theorems/039a58b0-e20f-4e34-b2c2-ccf02ae182b8
-- title:
--   OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq` of [lean/OAI/Probability/FreeIsing/Gibbs/CovarianceCriticalEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gibbs/CovarianceCriticalEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal Topology BigOperators`, `open PlantedSymmetry`):
--
--   ```lean
--   theorem HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq
--       {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
--       {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
--       (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
--       (hmB : ∀ i t, Measurable (B i t))
--       (hcB : ∀ i omega, Continuous (fun t => B i t omega))
--       (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
--       let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
--       let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
--       let M := ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (T, p)) ^ 2
--         ∂μ.prod (Measure.infinitePi ν)
--       HasSum (fun w => ∫ p, C w p ^ 2 ∂P) M ∧
--         (∫ p, ∑' w, C w p ^ 2 ∂P) = M
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.infiniteGibbsCovariance` and `OAI.Problem367.infiniteGibbsSpinMean` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.brownianIsingObservationR` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovarianceCompensator_tendsto_L1`, `OAI.Problem367.IsingInnovation.exists_posterior_integral_representation` and `OAI.Problem367.IsingInnovation.finiteCovariance_fullTime_interval_energy_cauchy` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gibbs/CovarianceCriticalEnergy.lean (declaration OAI.Problem367.HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq)

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
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
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators
namespace Problem367
open PlantedSymmetry

theorem HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
    let M := ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)
    HasSum (fun w => ∫ p, C w p ^ 2 ∂P) M ∧
      (∫ p, ∑' w, C w p ^ 2 ∂P) = M := by
  sorry

end Problem367

end

end OAI
end
