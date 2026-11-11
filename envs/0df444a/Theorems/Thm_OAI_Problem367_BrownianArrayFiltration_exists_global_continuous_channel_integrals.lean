-- Prove2me | Theorems.Thm_OAI_Problem367_BrownianArrayFiltration_exists_global_continuous_channel_integrals
-- name    : OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_channel_integrals
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:13.803816+00:00
-- url     : https://prove2.me/theorems/bd2201ac-55e0-48e1-8136-b75a79a53b02
-- title:
--   OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_channel_integrals: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_channel_integrals` of [lean/OAI/Probability/FreeIsing/Brownian/ContinuousCross.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Brownian/ContinuousCross.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.BrownianArrayFiltration`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`):
--
--   ```lean
--   theorem exists_global_continuous_channel_integrals
--       (hB : ∀ a, IsPreBrownianReal (B a) P)
--       (hAd : ∀ a, StronglyAdapted F (B a))
--       (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
--         (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
--       (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
--         IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
--       (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
--       (hH : ∀ a, StronglyAdapted F (H a))
--       (hHc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
--       {K : ι → ℝ} (hK : ∀ a, 0 ≤ K a)
--       (hbound : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ K a) :
--       ∃ I : ι → ℝ≥0 → Ω → ℝ,
--         (∀ a, IsStronglyPredictable F (I a)) ∧
--         (∀ a, Martingale (I a) F P) ∧
--         (∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω)) ∧
--         (∀ a t, MemLp (I a t) 2 P) ∧
--         (∀ a, I a 0 =ᵐ[P] 0) ∧
--         (∀ a t, (∫ ω, I a t ω ∂P) = 0) ∧
--         (∀ a t, (∫ ω, (I a t ω) ^ 2 ∂P) =
--           ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, (H a s.toNNReal ω) ^ 2 ∂P) ∧
--         (∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
--           Tendsto (fun n => ∫ ω,
--             (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω - I a t ω) ^ 2 ∂P)
--             atTop (𝓝 0)) ∧
--         (Pairwise fun a b => Martingale (fun t ω => I a t ω * I b t ω) F P)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.BrownianIntegralProcess.stoppedUniformSum` (definitions bundle `Q243FI001` of this split).
--
--   **Used by.** The proof of `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_compensatedSquare` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Brownian/ContinuousCross.lean (declaration OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_channel_integrals)

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
  {B H I : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem exists_global_continuous_channel_integrals
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hH : ∀ a, StronglyAdapted F (H a))
    (hHc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    {K : ι → ℝ} (hK : ∀ a, 0 ≤ K a)
    (hbound : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ K a) :
    ∃ I : ι → ℝ≥0 → Ω → ℝ,
      (∀ a, IsStronglyPredictable F (I a)) ∧
      (∀ a, Martingale (I a) F P) ∧
      (∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω)) ∧
      (∀ a t, MemLp (I a t) 2 P) ∧
      (∀ a, I a 0 =ᵐ[P] 0) ∧
      (∀ a t, (∫ ω, I a t ω ∂P) = 0) ∧
      (∀ a t, (∫ ω, (I a t ω) ^ 2 ∂P) =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, (H a s.toNNReal ω) ^ 2 ∂P) ∧
      (∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ ω,
          (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω - I a t ω) ^ 2 ∂P)
          atTop (𝓝 0)) ∧
      (Pairwise fun a b => Martingale (fun t ω => I a t ω * I b t ω) F P) := by
  sorry

end Problem367.BrownianArrayFiltration

end

end OAI
end
