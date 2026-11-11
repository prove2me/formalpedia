-- Prove2me | Theorems.Thm_OAI_Problem367_FiniteIsingFiltering_exists_innovation_integral_representation
-- name    : OAI.Problem367.FiniteIsingFiltering.exists_innovation_integral_representation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:43:01.209176+00:00
-- url     : https://prove2.me/theorems/10c134b7-d925-45be-80bd-b8cc44f53629
-- title:
--   OAI.Problem367.FiniteIsingFiltering.exists_innovation_integral_representation: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.FiniteIsingFiltering.exists_innovation_integral_representation` of [lean/OAI/Probability/FreeIsing/Stochastic/FiniteIsingFilteringIntegral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Stochastic/FiniteIsingFilteringIntegral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.FiniteIsingFiltering`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal ENNReal Topology BigOperators`):
--
--   ```lean
--   theorem exists_innovation_integral_representation
--       {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
--       (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
--       (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
--       (hmB : ∀ i t, Measurable (B i t))
--       (hcB : ∀ i omega, Continuous (fun t => B i t omega))
--       (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (T : ℝ≥0) :
--       ∃ I : D → State d Ω → ℝ,
--         (∀ u, MemLp (I u) 2 (μ.prod (Measure.infinitePi ν))) ∧
--         (∀ u, AEStronglyMeasurable[observationFiltration B hmB D T]
--           (I u) (μ.prod (Measure.infinitePi ν))) ∧
--         (∀ u, (∫ p, I u p ∂μ.prod (Measure.infinitePi ν)) = 0) ∧
--         (∀ u, (∫ p, I u p ^ 2 ∂μ.prod (Measure.infinitePi ν)) =
--           ∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
--             covariance beta D v u B r.toNNReal p ^ 2 ∂μ.prod (Measure.infinitePi ν)) ∧
--         (Pairwise fun u w => ∫ p, I u p * I w p ∂μ.prod (Measure.infinitePi ν) = 0) ∧
--         (∀ u, Tendsto (fun n => ∫ p,
--           (BrownianGrid.uniformSum (innovation beta D u B) (covariance beta D v u B) T n p - I u p) ^ 2
--             ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0)) ∧
--         (mean beta D v B T =ᵐ[μ.prod (Measure.infinitePi ν)] fun p => ∑ u, I u p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.BrownianGrid.uniformSum` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.FiniteIsingFiltering.State`, `OAI.Problem367.FiniteIsingFiltering.covariance`, `OAI.Problem367.FiniteIsingFiltering.innovation`, `OAI.Problem367.FiniteIsingFiltering.mean` and `OAI.Problem367.FiniteIsingFiltering.observationFiltration` (definitions bundle `Q243FI003` of this split); `OAI.Problem367.ConnectedFinset`, `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.FiniteIsingFiltering.mean_compensatedSquare_martingale` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Stochastic/FiniteIsingFilteringIntegral.lean (declaration OAI.Problem367.FiniteIsingFiltering.exists_innovation_integral_representation)

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI003

section

attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem exists_innovation_integral_representation
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (T : ℝ≥0) :
    ∃ I : D → State d Ω → ℝ,
      (∀ u, MemLp (I u) 2 (μ.prod (Measure.infinitePi ν))) ∧
      (∀ u, AEStronglyMeasurable[observationFiltration B hmB D T]
        (I u) (μ.prod (Measure.infinitePi ν))) ∧
      (∀ u, (∫ p, I u p ∂μ.prod (Measure.infinitePi ν)) = 0) ∧
      (∀ u, (∫ p, I u p ^ 2 ∂μ.prod (Measure.infinitePi ν)) =
        ∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
          covariance beta D v u B r.toNNReal p ^ 2 ∂μ.prod (Measure.infinitePi ν)) ∧
      (Pairwise fun u w => ∫ p, I u p * I w p ∂μ.prod (Measure.infinitePi ν) = 0) ∧
      (∀ u, Tendsto (fun n => ∫ p,
        (BrownianGrid.uniformSum (innovation beta D u B) (covariance beta D v u B) T n p - I u p) ^ 2
          ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0)) ∧
      (mean beta D v B T =ᵐ[μ.prod (Measure.infinitePi ν)] fun p => ∑ u, I u p) := by
  sorry

end Problem367.FiniteIsingFiltering

end

end OAI
end
