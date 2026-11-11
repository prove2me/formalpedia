-- Prove2me | Theorems.Thm_OAI_Problem367_IsingInnovation_exists_posterior_integral_representation
-- name    : OAI.Problem367.IsingInnovation.exists_posterior_integral_representation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:01.099466+00:00
-- url     : https://prove2.me/theorems/536d8d66-1cfc-4349-b5ac-544186169f40
-- title:
--   OAI.Problem367.IsingInnovation.exists_posterior_integral_representation: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingInnovation.exists_posterior_integral_representation` of [lean/OAI/Probability/FreeIsing/Ising/PosteriorIntegralRepresentation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/PosteriorIntegralRepresentation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingInnovation`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`):
--
--   ```lean
--   theorem exists_posterior_integral_representation
--       {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
--       (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
--       (v : TreeVertex d) (T : ℝ≥0) :
--       let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
--       ∃ (X : ℕ → TreeVertex d → State d A → ℝ) (I : TreeVertex d → State d A → ℝ)
--         (hI : ∀ u, MemLp (I u) 2 P) (hM : MemLp (posterior beta B v T) 2 P),
--         (∀ n u, MemLp (X n u) 2 P) ∧
--         (∀ n u, Tendsto (fun k => ∫ q,
--           (BrownianGrid.uniformSum (innovation beta B u) (finiteCovariance beta B v u n)
--             T k q - X n u q) ^ 2 ∂P) atTop (𝓝 0)) ∧
--         (∀ u, Tendsto (fun n => ∫ q, (X n u q - I u q) ^ 2 ∂P) atTop (𝓝 0)) ∧
--         (∀ u, Measurable (I u)) ∧
--         (∀ u, AEStronglyMeasurable[ArrayPosteriorStationarity.filtration B hmB T] (I u) P) ∧
--         (∀ u, (∫ q, I u q ∂P) = 0) ∧
--         HasSum (fun u => (hI u).toLp (I u)) (hM.toLp (posterior beta B v T)) ∧
--         Tendsto (fun s : Finset (TreeVertex d) => ∫ q,
--           ((∑ u ∈ s, I u q) - posterior beta B v T q) ^ 2 ∂P) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingInnovation.State`, `OAI.Problem367.IsingInnovation.innovation` and `OAI.Problem367.IsingInnovation.posterior` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.BrownianGrid.uniformSum` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.ArrayPosteriorStationarity.filtration` (definitions bundle `Q243FI003` of this split); `OAI.Problem367.IsingInnovation.finiteCovariance` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.IsingInnovation.exists_continuous_posterior` and `OAI.Problem367.IsingObservationFactor.exists_canonical_root_covariance_integral_representation` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/PosteriorIntegralRepresentation.lean (declaration OAI.Problem367.IsingInnovation.exists_posterior_integral_representation)

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI003
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
open scoped NNReal Topology

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem exists_posterior_integral_representation
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) (T : ℝ≥0) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    ∃ (X : ℕ → TreeVertex d → State d A → ℝ) (I : TreeVertex d → State d A → ℝ)
      (hI : ∀ u, MemLp (I u) 2 P) (hM : MemLp (posterior beta B v T) 2 P),
      (∀ n u, MemLp (X n u) 2 P) ∧
      (∀ n u, Tendsto (fun k => ∫ q,
        (BrownianGrid.uniformSum (innovation beta B u) (finiteCovariance beta B v u n)
          T k q - X n u q) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ u, Tendsto (fun n => ∫ q, (X n u q - I u q) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ u, Measurable (I u)) ∧
      (∀ u, AEStronglyMeasurable[ArrayPosteriorStationarity.filtration B hmB T] (I u) P) ∧
      (∀ u, (∫ q, I u q ∂P) = 0) ∧
      HasSum (fun u => (hI u).toLp (I u)) (hM.toLp (posterior beta B v T)) ∧
      Tendsto (fun s : Finset (TreeVertex d) => ∫ q,
        ((∑ u ∈ s, I u q) - posterior beta B v T q) ^ 2 ∂P) atTop (𝓝 0) := by
  sorry

end Problem367.IsingInnovation

end

end OAI
end
