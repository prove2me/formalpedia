-- Prove2me | Theorems.Thm_OAI_Problem367_BrownianIntegralProcess_exists_global_continuous_uniform_integral
-- name    : OAI.Problem367.BrownianIntegralProcess.exists_global_continuous_uniform_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:12.402897+00:00
-- url     : https://prove2.me/theorems/01d99194-306d-4b4f-bbbe-d8ff5d273ff5
-- title:
--   OAI.Problem367.BrownianIntegralProcess.exists_global_continuous_uniform_integral: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.BrownianIntegralProcess.exists_global_continuous_uniform_integral` of [lean/OAI/Probability/FreeIsing/Brownian/IntegralHorizon.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Brownian/IntegralHorizon.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.BrownianIntegralProcess`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal Topology`):
--
--   ```lean
--   theorem exists_global_continuous_uniform_integral
--       {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
--       (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
--       (hind : ∀ s t, s ≤ t → Indep
--         (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
--       (hBc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
--       (hH : StronglyAdapted F H)
--       (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
--       {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) :
--       ∃ I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F I ∧ Martingale I F P ∧
--         (∀ᵐ ω ∂P, Continuous (fun t => I t ω)) ∧
--         (∀ t, MemLp (I t) 2 P) ∧ I 0 =ᵐ[P] 0 ∧
--         (∀ t, (∫ ω, I t ω ∂P) = 0) ∧
--         (∀ t, (∫ ω, (I t ω) ^ 2 ∂P) =
--           ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, (H s.toNNReal ω) ^ 2 ∂P) ∧
--         (∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
--           Tendsto (fun n => ∫ ω,
--             (stoppedUniformSum B H N n t ω - I t ω) ^ 2 ∂P) atTop (𝓝 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.BrownianIntegralProcess.stoppedUniformSum` (definitions bundle `Q243FI001` of this split).
--
--   **Used by.** The proofs of `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_channel_integrals`, `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral` and `OAI.Problem367.IsingObservationFactor.exists_canonical_root_covariance_integral_representation` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Brownian/IntegralHorizon.lean (declaration OAI.Problem367.BrownianIntegralProcess.exists_global_continuous_uniform_integral)

import Mathlib
import Definitions.Def_Q243FI001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem exists_global_continuous_uniform_integral
    {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hBc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F I ∧ Martingale I F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => I t ω)) ∧
      (∀ t, MemLp (I t) 2 P) ∧ I 0 =ᵐ[P] 0 ∧
      (∀ t, (∫ ω, I t ω ∂P) = 0) ∧
      (∀ t, (∫ ω, (I t ω) ^ 2 ∂P) =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, (H s.toNNReal ω) ^ 2 ∂P) ∧
      (∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ ω,
          (stoppedUniformSum B H N n t ω - I t ω) ^ 2 ∂P) atTop (𝓝 0)) := by
  sorry

end Problem367.BrownianIntegralProcess

end

end OAI
end
