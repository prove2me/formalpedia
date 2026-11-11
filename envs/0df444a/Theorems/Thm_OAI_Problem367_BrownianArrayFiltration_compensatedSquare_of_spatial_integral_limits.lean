-- Prove2me | Theorems.Thm_OAI_Problem367_BrownianArrayFiltration_compensatedSquare_of_spatial_integral_limits
-- name    : OAI.Problem367.BrownianArrayFiltration.compensatedSquare_of_spatial_integral_limits
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:59.404894+00:00
-- url     : https://prove2.me/theorems/ce6c34f6-a012-4c2f-a248-c03bb114f8cd
-- title:
--   OAI.Problem367.BrownianArrayFiltration.compensatedSquare_of_spatial_integral_limits: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.BrownianArrayFiltration.compensatedSquare_of_spatial_integral_limits` of [lean/OAI/Probability/FreeIsing/Conditioning/CopyCompensatedSquare.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Conditioning/CopyCompensatedSquare.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.BrownianArrayFiltration`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`):
--
--   ```lean
--   theorem compensatedSquare_of_spatial_integral_limits
--       [Countable ι] [IsProbabilityMeasure P]
--       {F : Filtration ℝ≥0 mΩ} {B H I : ι → ℝ≥0 → Ω → ℝ}
--       {Y : ℝ≥0 → Ω → ℝ}
--       (hB : ∀ a, IsPreBrownianReal (B a) P)
--       (hAd : ∀ a, StronglyAdapted F (B a))
--       (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
--         (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
--       (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
--         IndepFun (fun ω => B a t ω - B a s ω)
--           (fun ω => B b t ω - B b s ω) P)
--       (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
--       (hH : ∀ a, IsStronglyProgressive F (H a))
--       (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
--       {C : ι → ℝ} (hC : ∀ a, 0 ≤ C a)
--       (hb : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
--       (henergy : ∀ N : ℕ, Summable (fun a =>
--         ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P))
--       (hI2 : ∀ a t, MemLp (I a t) 2 P)
--       (hYad : StronglyAdapted F Y) (hY2 : ∀ t, MemLp (Y t) 2 P)
--       (hlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
--         Tendsto (fun n => ∫ ω,
--           (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω -
--             I a t ω) ^ 2 ∂P) atTop (𝓝 0))
--       (hsum : ∀ t, HasSum (fun a => (hI2 a t).toLp (I a t))
--         ((hY2 t).toLp (Y t))) :
--       Martingale Y F P ∧
--         Martingale (fun t ω => Y t ω ^ 2 -
--           nnrealTimePrimitive (spatialSquareDensity H) t ω) F P
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.nnrealTimePrimitive` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.BrownianArrayFiltration.spatialSquareDensity` and `OAI.Problem367.BrownianIntegralProcess.stoppedUniformSum` (definitions bundle `Q243FI001` of this split).
--
--   **Used by.** The proof of `OAI.Problem367.IsingJoinedResponseIntegrals.exists_integrals` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Conditioning/CopyCompensatedSquare.lean (declaration OAI.Problem367.BrownianArrayFiltration.compensatedSquare_of_spatial_integral_limits)

import Mathlib
import Definitions.Def_Q243FI000
import Definitions.Def_Q243FI001

section

attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
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

theorem compensatedSquare_of_spatial_integral_limits
    [Countable ι] [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B H I : ι → ℝ≥0 → Ω → ℝ}
    {Y : ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω)
        (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hH : ∀ a, IsStronglyProgressive F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    {C : ι → ℝ} (hC : ∀ a, 0 ≤ C a)
    (hb : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (henergy : ∀ N : ℕ, Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P))
    (hI2 : ∀ a t, MemLp (I a t) 2 P)
    (hYad : StronglyAdapted F Y) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω -
          I a t ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsum : ∀ t, HasSum (fun a => (hI2 a t).toLp (I a t))
      ((hY2 t).toLp (Y t))) :
    Martingale Y F P ∧
      Martingale (fun t ω => Y t ω ^ 2 -
        nnrealTimePrimitive (spatialSquareDensity H) t ω) F P := by
  sorry

end Problem367.BrownianArrayFiltration

end

end OAI
end
