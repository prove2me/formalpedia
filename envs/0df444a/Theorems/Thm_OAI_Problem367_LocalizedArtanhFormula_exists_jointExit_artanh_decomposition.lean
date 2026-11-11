-- Prove2me | Theorems.Thm_OAI_Problem367_LocalizedArtanhFormula_exists_jointExit_artanh_decomposition
-- name    : OAI.Problem367.LocalizedArtanhFormula.exists_jointExit_artanh_decomposition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:39:19.729227+00:00
-- url     : https://prove2.me/theorems/4add12bd-bfe9-4cc4-8446-60b8838b7c75
-- title:
--   OAI.Problem367.LocalizedArtanhFormula.exists_jointExit_artanh_decomposition: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.LocalizedArtanhFormula.exists_jointExit_artanh_decomposition` of [lean/OAI/Probability/FreeIsing/Estimates/LocalizedArtanhFormula.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Estimates/LocalizedArtanhFormula.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.LocalizedArtanhFormula`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal Topology`, `open ArtanhMartingaleFormula PosteriorStoppingTimes PosteriorCompensatorStopping`, `open StoppedTimePrimitive`):
--
--   ```lean
--   theorem exists_jointExit_artanh_decomposition [IsProbabilityMeasure μ]
--       {F : Filtration ℝ≥0 mΩ} {M a : ℝ≥0 → Ω → ℝ}
--       (hM : Martingale M F μ)
--       (hQ : Martingale (fun t ω => M t ω ^ 2 - nnrealTimePrimitive a t ω) F μ)
--       (hprogM : IsStronglyProgressive F M) (hproga : IsStronglyProgressive F a)
--       (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
--       (hzero : ∀ᵐ ω ∂μ, M 0 ω = 0)
--       (hbound : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ 1)
--       (hnonneg : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ a t ω)
--       (ha : ∀ T : ℝ≥0, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
--         ((volume.restrict (Ioc (0 : ℝ) T)).prod μ))
--       (n : ℕ) (T : ℝ≥0) :
--       let τ := jointExit M (nnrealTimePrimitive a) n
--       let N := stoppedProcess M τ
--       ∃ L : Ω → ℝ, StronglyMeasurable L ∧ MemLp L 2 μ ∧
--         Tendsto (fun k => ∫ ω,
--           (BrownianGrid.uniformSum N (fun t ω => firstWeight (N t ω)) T k ω - L ω) ^ 2 ∂μ)
--           atTop (𝓝 0) ∧
--         (fun ω => Real.artanh (N T ω) - Real.artanh (M 0 ω)) =ᵐ[μ]
--           fun ω => L ω + stoppedProcess
--             (nnrealTimePrimitive (fun t ω => secondWeight (M t ω) * a t ω)) τ T ω
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.nnrealTimePrimitive` and `OAI.Problem367.ArtanhMartingaleFormula.secondWeight` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.ArtanhMartingaleFormula.firstWeight`, `OAI.Problem367.BrownianGrid.uniformSum` and `OAI.Problem367.PosteriorCompensatorStopping.jointExit` (definitions bundle `Q243FI001` of this split).
--
--   **Used by.** The proof of `OAI.Problem367.IsingObservationFactor.canonical_artanh_decomposition` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Estimates/LocalizedArtanhFormula.lean (declaration OAI.Problem367.LocalizedArtanhFormula.exists_jointExit_artanh_decomposition)

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Process.Stopping
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
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.LocalizedArtanhFormula
open ArtanhMartingaleFormula PosteriorStoppingTimes PosteriorCompensatorStopping
open StoppedTimePrimitive

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem exists_jointExit_artanh_decomposition [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M a : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - nnrealTimePrimitive a t ω) F μ)
    (hprogM : IsStronglyProgressive F M) (hproga : IsStronglyProgressive F a)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hzero : ∀ᵐ ω ∂μ, M 0 ω = 0)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ 1)
    (hnonneg : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ a t ω)
    (ha : ∀ T : ℝ≥0, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ))
    (n : ℕ) (T : ℝ≥0) :
    let τ := jointExit M (nnrealTimePrimitive a) n
    let N := stoppedProcess M τ
    ∃ L : Ω → ℝ, StronglyMeasurable L ∧ MemLp L 2 μ ∧
      Tendsto (fun k => ∫ ω,
        (BrownianGrid.uniformSum N (fun t ω => firstWeight (N t ω)) T k ω - L ω) ^ 2 ∂μ)
        atTop (𝓝 0) ∧
      (fun ω => Real.artanh (N T ω) - Real.artanh (M 0 ω)) =ᵐ[μ]
        fun ω => L ω + stoppedProcess
          (nnrealTimePrimitive (fun t ω => secondWeight (M t ω) * a t ω)) τ T ω := by
  sorry

end Problem367.LocalizedArtanhFormula

end

end OAI
end
