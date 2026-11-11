-- Prove2me | Theorems.Thm_OAI_Problem367_IsingInnovation_exists_continuous_covariance_integral
-- name    : OAI.Problem367.IsingInnovation.exists_continuous_covariance_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:43:35.639209+00:00
-- url     : https://prove2.me/theorems/632d767e-affb-4625-8085-2d74ec8fdc9b
-- title:
--   OAI.Problem367.IsingInnovation.exists_continuous_covariance_integral: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingInnovation.exists_continuous_covariance_integral` of [lean/OAI/Probability/FreeIsing/Ising/ContinuousCovarianceIntegral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/ContinuousCovarianceIntegral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingInnovation`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology BigOperators`):
--
--   ```lean
--   theorem exists_continuous_covariance_integral
--       (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
--       (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
--       (v : TreeVertex d) :
--       let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
--       let F := ArrayPosteriorStationarity.filtration B hmB
--       ∃ (I : ℕ → TreeVertex d → ℝ≥0 → State d A → ℝ)
--         (Y : ℕ → ℝ≥0 → State d A → ℝ) (Z : ℝ≥0 → State d A → ℝ)
--         (hI2 : ∀ n u t, MemLp (I n u t) 2 P)
--         (hY2 : ∀ n t, MemLp (Y n t) 2 P) (_hZ2 : ∀ t, MemLp (Z t) 2 P),
--         (∀ n, IsStronglyPredictable F (Y n) ∧ Martingale (Y n) F P ∧
--           (∀ᵐ q ∂P, Continuous (fun t => Y n t q))) ∧
--         (∀ n u (N : ℕ), 0 < N → Tendsto (fun k => ∫ q,
--           (BrownianGrid.uniformSum (innovation beta B u) (finiteCovariance beta B v u n)
--             N k q - I n u N q) ^ 2 ∂P) atTop (𝓝 0)) ∧
--         (∀ n t, HasSum (fun u => (hI2 n u t).toLp (I n u t))
--           ((hY2 n t).toLp (Y n t))) ∧
--         (∀ n t, (∫ q, Y n t q ^ 2 ∂P) =
--           ∑' u, ∫ s in (0 : ℝ)..(t : ℝ),
--             ∫ q, finiteCovariance beta B v u n s.toNNReal q ^ 2 ∂P) ∧
--         (∀ n m (N : ℕ), 0 < N → (∫ q, (Y n N q - Y m N q) ^ 2 ∂P) =
--           ∑' u, ∫ s in (0 : ℝ)..(N : ℝ), ∫ q,
--             (finiteCovariance beta B v u n s.toNNReal q -
--               finiteCovariance beta B v u m s.toNNReal q) ^ 2 ∂P) ∧
--         IsStronglyPredictable F Z ∧ Martingale Z F P ∧
--         (∀ᵐ q ∂P, Continuous (fun t => Z t q)) ∧ Z 0 =ᵐ[P] 0 ∧
--         (∀ t, (∫ q, Z t q ∂P) = 0) ∧
--         (∀ t, Tendsto (fun n => ∫ q, (Y n t q - Z t q) ^ 2 ∂P) atTop (𝓝 0)) ∧
--         (∀ t : ℝ≥0, Tendsto (fun n => ∑' u, ∫ s in (0 : ℝ)..(t : ℝ),
--           ∫ q, finiteCovariance beta B v u n s.toNNReal q ^ 2 ∂P) atTop
--             (𝓝 (∫ q, Z t q ^ 2 ∂P))) ∧
--         (∀ T, Tendsto (fun n => ∫ q,
--           MartingaleStrongMaximal.maximalSquare (Y n - Z) T q ∂P) atTop (𝓝 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.IsingInnovation.State` and `OAI.Problem367.IsingInnovation.innovation` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.BrownianGrid.uniformSum` and `OAI.Problem367.MartingaleStrongMaximal.maximalSquare` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.ArrayPosteriorStationarity.filtration` (definitions bundle `Q243FI003` of this split); `OAI.Problem367.IsingInnovation.finiteCovariance` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingInnovation.exists_continuous_posterior` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/ContinuousCovarianceIntegral.lean (declaration OAI.Problem367.IsingInnovation.exists_continuous_covariance_integral)

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
open scoped NNReal Topology BigOperators

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem exists_continuous_covariance_integral
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let F := ArrayPosteriorStationarity.filtration B hmB
    ∃ (I : ℕ → TreeVertex d → ℝ≥0 → State d A → ℝ)
      (Y : ℕ → ℝ≥0 → State d A → ℝ) (Z : ℝ≥0 → State d A → ℝ)
      (hI2 : ∀ n u t, MemLp (I n u t) 2 P)
      (hY2 : ∀ n t, MemLp (Y n t) 2 P) (_hZ2 : ∀ t, MemLp (Z t) 2 P),
      (∀ n, IsStronglyPredictable F (Y n) ∧ Martingale (Y n) F P ∧
        (∀ᵐ q ∂P, Continuous (fun t => Y n t q))) ∧
      (∀ n u (N : ℕ), 0 < N → Tendsto (fun k => ∫ q,
        (BrownianGrid.uniformSum (innovation beta B u) (finiteCovariance beta B v u n)
          N k q - I n u N q) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ n t, HasSum (fun u => (hI2 n u t).toLp (I n u t))
        ((hY2 n t).toLp (Y n t))) ∧
      (∀ n t, (∫ q, Y n t q ^ 2 ∂P) =
        ∑' u, ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ q, finiteCovariance beta B v u n s.toNNReal q ^ 2 ∂P) ∧
      (∀ n m (N : ℕ), 0 < N → (∫ q, (Y n N q - Y m N q) ^ 2 ∂P) =
        ∑' u, ∫ s in (0 : ℝ)..(N : ℝ), ∫ q,
          (finiteCovariance beta B v u n s.toNNReal q -
            finiteCovariance beta B v u m s.toNNReal q) ^ 2 ∂P) ∧
      IsStronglyPredictable F Z ∧ Martingale Z F P ∧
      (∀ᵐ q ∂P, Continuous (fun t => Z t q)) ∧ Z 0 =ᵐ[P] 0 ∧
      (∀ t, (∫ q, Z t q ∂P) = 0) ∧
      (∀ t, Tendsto (fun n => ∫ q, (Y n t q - Z t q) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ t : ℝ≥0, Tendsto (fun n => ∑' u, ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ q, finiteCovariance beta B v u n s.toNNReal q ^ 2 ∂P) atTop
          (𝓝 (∫ q, Z t q ^ 2 ∂P))) ∧
      (∀ T, Tendsto (fun n => ∫ q,
        MartingaleStrongMaximal.maximalSquare (Y n - Z) T q ∂P) atTop (𝓝 0)) := by
  sorry

end Problem367.IsingInnovation

end

end OAI
end
