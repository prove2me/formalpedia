-- Prove2me | Theorems.Thm_OAI_Problem367_BrownianArrayFiltration_exists_global_continuous_spatial_integral_compensatedSquare
-- name    : OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_compensatedSquare
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:05.628954+00:00
-- url     : https://prove2.me/theorems/0d4595dd-9f46-45b3-a40f-c97f9d1f9cce
-- title:
--   OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_compensatedSquare (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_compensatedSquare` of [lean/OAI/Probability/FreeIsing/Brownian/SpatialCompensator.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Brownian/SpatialCompensator.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.BrownianArrayFiltration`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal ENNReal Topology`):
--
--   ```lean
--   theorem exists_global_continuous_spatial_integral_compensatedSquare
--       [Countable ι] [IsProbabilityMeasure P]
--       {B H : ι → ℝ≥0 → Ω → ℝ}
--       (hB : ∀ a, IsPreBrownianReal (B a) P)
--       (hAd : ∀ a, StronglyAdapted F (B a))
--       (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
--         (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
--       (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
--         IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
--       (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
--       (hH : ∀ a, StronglyAdapted F (H a))
--       (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
--       {C : ι → ℝ} (hC : ∀ a, 0 ≤ C a)
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
--         (∀ t, (∫ ω, Y t ω ^ 2 ∂P) =
--           ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P) ∧
--         (∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t))) ∧
--         (∀ T : ℝ≥0, Tendsto (fun q : Finset ι =>
--           ∫ ω, MartingaleStrongMaximal.maximalSquare
--             (MartingaleSpatialLimit.finiteSum I q - Y) T ω ∂P) atTop (𝓝 0)) ∧
--         Martingale (fun t ω => Y t ω ^ 2 - spatialCompensator H t ω) F P ∧
--         (∀ t, Integrable (spatialCompensator H t) P) ∧
--         (∀ t, ∀ᵐ ω ∂P, Summable (fun a => nonnegativeCompensator (H a) t ω))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.BrownianArrayFiltration.nonnegativeCompensator`, `OAI.Problem367.BrownianArrayFiltration.spatialCompensator`, `OAI.Problem367.BrownianIntegralProcess.stoppedUniformSum`, `OAI.Problem367.MartingaleSpatialLimit.finiteSum` and `OAI.Problem367.MartingaleStrongMaximal.maximalSquare` (definitions bundle `Q243FI001` of this split).
--
--   **Used by.** The proofs of `OAI.Problem367.BrownianArrayFiltration.compensatedSquare_of_spatial_integral_limits`, `OAI.Problem367.IsingJoinedResponseIntegrals.exists_integrals` and `OAI.Problem367.IsingObservationFactor.actual_variance_analysis` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Brownian/SpatialCompensator.lean (declaration OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_compensatedSquare)

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
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ}

theorem exists_global_continuous_spatial_integral_compensatedSquare
    [Countable ι] [IsProbabilityMeasure P]
    {B H : ι → ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hH : ∀ a, StronglyAdapted F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    {C : ι → ℝ} (hC : ∀ a, 0 ≤ C a)
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
      (∀ t, (∫ ω, Y t ω ^ 2 ∂P) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P) ∧
      (∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t))) ∧
      (∀ T : ℝ≥0, Tendsto (fun q : Finset ι =>
        ∫ ω, MartingaleStrongMaximal.maximalSquare
          (MartingaleSpatialLimit.finiteSum I q - Y) T ω ∂P) atTop (𝓝 0)) ∧
      Martingale (fun t ω => Y t ω ^ 2 - spatialCompensator H t ω) F P ∧
      (∀ t, Integrable (spatialCompensator H t) P) ∧
      (∀ t, ∀ᵐ ω ∂P, Summable (fun a => nonnegativeCompensator (H a) t ω)) := by
  sorry

end Problem367.BrownianArrayFiltration

end

end OAI
end
