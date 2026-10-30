-- Prove2me | Theorems.Thm_OAI_Falconer_Regularization_uniform_regularizationPairExceptional_bound
-- name    : OAI.Falconer.Regularization.uniform_regularizationPairExceptional_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:46:51.986987+00:00
-- url     : https://prove2.me/theorems/fdfd4029-2cff-4500-b23f-924377d22ccc
-- title:
--   OAI.Falconer.Regularization.uniform_regularizationPairExceptional_bound: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.Regularization.uniform_regularizationPairExceptional_bound` of [lean/OAI/MeasureTheory/Falconer/Estimates/RegularizationPairBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/RegularizationPairBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer.Regularization`, with `open Set MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem uniform_regularizationPairExceptional_bound {σ : ℝ} (hσ : 0 < σ) :
--       ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q₁ Q₂ : DyadicCube d), Q₁.side = 1 → Q₂.side = 1 →
--         ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
--         ∀ (B₁ B₂ : ℕ), 0 < B₁ → 0 < B₂ →
--         (B₁:ℝ) ≤ σ*N → (B₂:ℝ) ≤ σ*N →
--         (2:ℝ)^(N/B₁+2) ≤ ((2:ℝ)^N)^σ → (2:ℝ)^(N/B₂+2) ≤ ((2:ℝ)^N)^σ →
--         ∀ (t₁ t₂ : ℝ≥0∞), 0 < t₁ → 0 < t₂ → ∀ p₁ p₂ : List ℕ → CellPath d,
--         (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, p₁ T ∈ regularizationLeaves Q₁ μ N) →
--         (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, p₂ T ∈ regularizationLeaves Q₂ ν N) →
--         (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, regularizationLabel Q₁ μ N B₁ (p₁ T) = T) →
--         (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, regularizationLabel Q₂ ν N B₂ (p₂ T) = T) →
--         ∀ (w₀ : Sphere d) (G : Set (Space d × Space d)), MeasurableSet G →
--         (∀ᵐ x ∂μ, ∀ u : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
--           originalRadialSphereLaw w₀ ν G x {w : Sphere d | dist (w:Space d) u < r} ≤
--             ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
--         (∀ᵐ y ∂ν, ∀ u : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
--           originalRadialSphereLaw w₀ μ (Prod.swap ⁻¹' G) y {w : Sphere d | dist (w:Space d) u < r} ≤
--             ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
--         ∀ κ : ℝ,
--         (μ.prod ν) (regularizationPairExceptional Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ w₀ G) ≤
--           μ (retainedRegion Q₁ μ N B₁ t₁)ᶜ + ν (retainedRegion Q₂ ν N B₂ t₂)ᶜ +
--             (4*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.DyadicCube`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere` and `OAI.Falconer.Regularization.CellPath` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.originalRadialSphereLaw`, `OAI.Falconer.Regularization.regularizationIndex`, `OAI.Falconer.Regularization.regularizationLabel`, `OAI.Falconer.Regularization.regularizationLeaves`, `OAI.Falconer.Regularization.regularizationPairExceptional` and `OAI.Falconer.Regularization.retainedRegion` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.prepared_pair_positive_distance` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/RegularizationPairBounds.lean (declaration OAI.Falconer.Regularization.uniform_regularizationPairExceptional_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem uniform_regularizationPairExceptional_bound {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q₁ Q₂ : DyadicCube d), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B₁ B₂ : ℕ), 0 < B₁ → 0 < B₂ →
      (B₁:ℝ) ≤ σ*N → (B₂:ℝ) ≤ σ*N →
      (2:ℝ)^(N/B₁+2) ≤ ((2:ℝ)^N)^σ → (2:ℝ)^(N/B₂+2) ≤ ((2:ℝ)^N)^σ →
      ∀ (t₁ t₂ : ℝ≥0∞), 0 < t₁ → 0 < t₂ → ∀ p₁ p₂ : List ℕ → CellPath d,
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, p₁ T ∈ regularizationLeaves Q₁ μ N) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, p₂ T ∈ regularizationLeaves Q₂ ν N) →
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, regularizationLabel Q₁ μ N B₁ (p₁ T) = T) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, regularizationLabel Q₂ ν N B₂ (p₂ T) = T) →
      ∀ (w₀ : Sphere d) (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ᵐ x ∂μ, ∀ u : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        originalRadialSphereLaw w₀ ν G x {w : Sphere d | dist (w:Space d) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
      (∀ᵐ y ∂ν, ∀ u : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        originalRadialSphereLaw w₀ μ (Prod.swap ⁻¹' G) y {w : Sphere d | dist (w:Space d) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
      ∀ κ : ℝ,
      (μ.prod ν) (regularizationPairExceptional Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ w₀ G) ≤
        μ (retainedRegion Q₁ μ N B₁ t₁)ᶜ + ν (retainedRegion Q₂ ν N B₂ t₂)ᶜ +
          (4*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ)) := by
  sorry

end Falconer.Regularization

end OAI
end
