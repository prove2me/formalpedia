-- Prove2me | Theorems.Thm_OAI_Problem367_IsingInnovation_finiteCovariance_fullTime_interval_energy_cauchy
-- name    : OAI.Problem367.IsingInnovation.finiteCovariance_fullTime_interval_energy_cauchy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:43:36.728605+00:00
-- url     : https://prove2.me/theorems/ac065867-a72c-452d-9641-e8290475c39f
-- title:
--   OAI.Problem367.IsingInnovation.finiteCovariance_fullTime_interval_energy_cauchy: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingInnovation.finiteCovariance_fullTime_interval_energy_cauchy` of [lean/OAI/Probability/FreeIsing/Ising/ContinuousCovarianceIntegral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/ContinuousCovarianceIntegral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingInnovation`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology BigOperators`):
--
--   ```lean
--   theorem finiteCovariance_fullTime_interval_energy_cauchy
--       (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
--       (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
--       (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
--       let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
--       (∀ n, Summable (fun u => ∫ t in (0 : ℝ)..T,
--         ∫ q, finiteCovariance beta B v u n t.toNNReal q ^ 2 ∂P)) ∧
--       (∀ n k, Summable (fun u => ∫ t in (0 : ℝ)..T,
--         ∫ q, (finiteCovariance beta B v u n t.toNNReal q -
--           finiteCovariance beta B v u k t.toNNReal q) ^ 2 ∂P)) ∧
--       ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
--         (∑' u, ∫ t in (0 : ℝ)..T,
--           ∫ q, (finiteCovariance beta B v u n t.toNNReal q -
--             finiteCovariance beta B v u k t.toNNReal q) ^ 2 ∂P) < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingInnovation.finiteCovariance` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingInnovation.exists_continuous_covariance_integral` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/ContinuousCovarianceIntegral.lean (declaration OAI.Problem367.IsingInnovation.finiteCovariance_fullTime_interval_energy_cauchy)

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI004

section

attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem finiteCovariance_fullTime_interval_energy_cauchy
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    (∀ n, Summable (fun u => ∫ t in (0 : ℝ)..T,
      ∫ q, finiteCovariance beta B v u n t.toNNReal q ^ 2 ∂P)) ∧
    (∀ n k, Summable (fun u => ∫ t in (0 : ℝ)..T,
      ∫ q, (finiteCovariance beta B v u n t.toNNReal q -
        finiteCovariance beta B v u k t.toNNReal q) ^ 2 ∂P)) ∧
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      (∑' u, ∫ t in (0 : ℝ)..T,
        ∫ q, (finiteCovariance beta B v u n t.toNNReal q -
          finiteCovariance beta B v u k t.toNNReal q) ^ 2 ∂P) < ε := by
  sorry

end Problem367.IsingInnovation

end

end OAI
end
