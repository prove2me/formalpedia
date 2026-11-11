-- Prove2me | Theorems.Thm_OAI_Problem367_ConstructedArtanhFormula_exists_artanh_decomposition
-- name    : OAI.Problem367.ConstructedArtanhFormula.exists_artanh_decomposition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:38:57.325251+00:00
-- url     : https://prove2.me/theorems/c541ccb2-8106-4c74-8aec-3afbcaa835d6
-- title:
--   OAI.Problem367.ConstructedArtanhFormula.exists_artanh_decomposition: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.ConstructedArtanhFormula.exists_artanh_decomposition` of [lean/OAI/Probability/FreeIsing/Estimates/ConstructedArtanhFormula.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Estimates/ConstructedArtanhFormula.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.ConstructedArtanhFormula`, with `open MeasureTheory Filter Set`, `open scoped NNReal Topology`, `open ArtanhMartingaleFormula`):
--
--   ```lean
--   theorem exists_artanh_decomposition [IsProbabilityMeasure μ]
--       {F : Filtration ℝ≥0 mΩ} {M A a : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
--       (hM : Martingale M F μ)
--       (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
--       (hMm : Measurable (fun p : ℝ≥0 × Ω => M p.1 p.2))
--       (hcM : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Icc 0 T))
--       (hcA : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) (Icc 0 T))
--       (hmonoA : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) (Icc 0 T))
--       {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
--       (hbound : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ r)
--       {C : ℝ} (hC : 0 ≤ C) (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C)
--       (ha : Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
--         ((volume.restrict (Ioc (0 : ℝ) T)).prod μ))
--       (hprimitive : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
--         A t ω = A 0 ω + nnrealTimePrimitive a t ω) :
--       ∃ L : Ω → ℝ, StronglyMeasurable L ∧ MemLp L 2 μ ∧
--         Tendsto (fun n => ∫ ω,
--           (BrownianGrid.uniformSum M (fun t ω => firstWeight (M t ω)) T n ω - L ω) ^ 2 ∂μ)
--           atTop (𝓝 0) ∧
--         (fun ω => Real.artanh (M T ω) - Real.artanh (M 0 ω)) =ᵐ[μ]
--           fun ω => L ω + nnrealTimePrimitive
--             (fun t ω => secondWeight (M t ω) * a t ω) T ω
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.nnrealTimePrimitive` and `OAI.Problem367.ArtanhMartingaleFormula.secondWeight` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.ArtanhMartingaleFormula.firstWeight` and `OAI.Problem367.BrownianGrid.uniformSum` (definitions bundle `Q243FI001` of this split).
--
--   **Used by.** The proof of `OAI.Problem367.LocalizedArtanhFormula.exists_jointExit_artanh_decomposition` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Estimates/ConstructedArtanhFormula.lean (declaration OAI.Problem367.ConstructedArtanhFormula.exists_artanh_decomposition)

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
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ConstructedArtanhFormula

open ArtanhMartingaleFormula

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem exists_artanh_decomposition [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A a : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hMm : Measurable (fun p : ℝ≥0 × Ω => M p.1 p.2))
    (hcM : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Icc 0 T))
    (hcA : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) (Icc 0 T))
    (hmonoA : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) (Icc 0 T))
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ r)
    {C : ℝ} (hC : 0 ≤ C) (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C)
    (ha : Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ))
    (hprimitive : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      A t ω = A 0 ω + nnrealTimePrimitive a t ω) :
    ∃ L : Ω → ℝ, StronglyMeasurable L ∧ MemLp L 2 μ ∧
      Tendsto (fun n => ∫ ω,
        (BrownianGrid.uniformSum M (fun t ω => firstWeight (M t ω)) T n ω - L ω) ^ 2 ∂μ)
        atTop (𝓝 0) ∧
      (fun ω => Real.artanh (M T ω) - Real.artanh (M 0 ω)) =ᵐ[μ]
        fun ω => L ω + nnrealTimePrimitive
          (fun t ω => secondWeight (M t ω) * a t ω) T ω := by
  sorry

end Problem367.ConstructedArtanhFormula

end

end OAI
end
