-- Prove2me | Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_finiteGibbsCovarianceCompensator_tendsto_L1
-- name    : OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovarianceCompensator_tendsto_L1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:37.519145+00:00
-- url     : https://prove2.me/theorems/6bcde1fb-ff78-4a1c-b8e6-fe465493f0e8
-- title:
--   OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovarianceCompensator_tendsto_L1: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovarianceCompensator_tendsto_L1` of [lean/OAI/Probability/FreeIsing/Gibbs/CovarianceCompensator.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gibbs/CovarianceCompensator.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal Topology`):
--
--   ```lean
--   theorem HasFreeIsingLaw.finiteGibbsCovarianceCompensator_tendsto_L1
--       {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
--       {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
--       (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
--       (hmB : ∀ i t, Measurable (B i t))
--       (hcB : ∀ i omega, Continuous (fun t => B i t omega))
--       (v : TreeVertex d) (t : ℝ≥0) :
--       Tendsto (fun n => eLpNorm
--         (finiteGibbsCovarianceCompensator beta v n B t - gibbsCovarianceCompensator beta v B t)
--         1 (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.finiteGibbsCovarianceCompensator` and `OAI.Problem367.gibbsCovarianceCompensator` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingObservationFactor.canonical_compensatedSquare_martingale` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Gibbs/CovarianceCompensator.lean (declaration OAI.Problem367.HasFreeIsingLaw.finiteGibbsCovarianceCompensator_tendsto_L1)

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section

attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367

theorem HasFreeIsingLaw.finiteGibbsCovarianceCompensator_tendsto_L1
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) (t : ℝ≥0) :
    Tendsto (fun n => eLpNorm
      (finiteGibbsCovarianceCompensator beta v n B t - gibbsCovarianceCompensator beta v B t)
      1 (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0) := by
  sorry

end Problem367

end

end OAI
end
