-- Prove2me | Theorems.Thm_OAI_Problem367_BrownianArrayFiltration_exists_global_continuous_spatial_integral
-- name    : OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:38:58.861247+00:00
-- url     : https://prove2.me/theorems/3ae453bf-cb2f-41a9-8e59-d6b5e496fb23
-- title:
--   OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral` of [lean/OAI/Probability/FreeIsing/Brownian/ContinuousSpatialIntegral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Brownian/ContinuousSpatialIntegral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.BrownianArrayFiltration`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`):
--
--   ```lean
--   theorem exists_global_continuous_spatial_integral [Countable ι] [IsProbabilityMeasure P]
--       (hB : ∀ a, IsPreBrownianReal (B a) P)
--       (hAd : ∀ a, StronglyAdapted F (B a))
--       (hind : ∀ s t, s ≤ t → Indep
--         (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
--       (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
--         IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
--       (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
--       (H : ι → ℝ≥0 → Ω → ℝ) (hH : ∀ a, StronglyAdapted F (H a))
--       (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
--       (C : ι → ℝ) (hC : ∀ a, 0 ≤ C a)
--       (hb : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
--       (henergy : ∀ N : ℕ, Summable (fun a =>
--         ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P)) :
--       ∃ (I : ι → ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ)
--         (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P),
--         (∀ a, IsStronglyPredictable F (I a) ∧ Martingale (I a) F P ∧
--           (∀ᵐ ω ∂P, Continuous (fun t => I a t ω))) ∧
--         (∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
--           Tendsto (fun n => ∫ ω,
--             (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω - I a t ω) ^ 2 ∂P)
--             atTop (𝓝 0)) ∧
--         IsStronglyPredictable F Y ∧ Martingale Y F P ∧
--         (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧ Y 0 =ᵐ[P] 0 ∧
--         (∀ t, (∫ ω, Y t ω ∂P) = 0) ∧
--         (∀ t, (∫ ω, Y t ω ^ 2 ∂P) =
--           ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P) ∧
--         (∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t))) ∧
--         (∀ T : ℝ≥0, Tendsto (fun q : Finset ι =>
--           ∫ ω, MartingaleStrongMaximal.maximalSquare
--             (MartingaleSpatialLimit.finiteSum I q - Y) T ω ∂P) atTop (𝓝 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.BrownianIntegralProcess.stoppedUniformSum`, `OAI.Problem367.MartingaleSpatialLimit.finiteSum` and `OAI.Problem367.MartingaleStrongMaximal.maximalSquare` (definitions bundle `Q243FI001` of this split).
--
--   **Used by.** The proof of `OAI.Problem367.IsingInnovation.exists_continuous_covariance_integral` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Brownian/ContinuousSpatialIntegral.lean (declaration OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral)

import Mathlib
import Definitions.Def_Q243FI001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem exists_global_continuous_spatial_integral [Countable ι] [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (H : ι → ℝ≥0 → Ω → ℝ) (hH : ∀ a, StronglyAdapted F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (C : ι → ℝ) (hC : ∀ a, 0 ≤ C a)
    (hb : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (henergy : ∀ N : ℕ, Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P)) :
    ∃ (I : ι → ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ)
      (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P),
      (∀ a, IsStronglyPredictable F (I a) ∧ Martingale (I a) F P ∧
        (∀ᵐ ω ∂P, Continuous (fun t => I a t ω))) ∧
      (∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ ω,
          (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω - I a t ω) ^ 2 ∂P)
          atTop (𝓝 0)) ∧
      IsStronglyPredictable F Y ∧ Martingale Y F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧ Y 0 =ᵐ[P] 0 ∧
      (∀ t, (∫ ω, Y t ω ∂P) = 0) ∧
      (∀ t, (∫ ω, Y t ω ^ 2 ∂P) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P) ∧
      (∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t))) ∧
      (∀ T : ℝ≥0, Tendsto (fun q : Finset ι =>
        ∫ ω, MartingaleStrongMaximal.maximalSquare
          (MartingaleSpatialLimit.finiteSum I q - Y) T ω ∂P) atTop (𝓝 0)) := by
  sorry

end Problem367.BrownianArrayFiltration

end

end OAI
end
