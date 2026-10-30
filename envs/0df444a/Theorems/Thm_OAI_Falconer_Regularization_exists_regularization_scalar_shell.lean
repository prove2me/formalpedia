-- Prove2me | Theorems.Thm_OAI_Falconer_Regularization_exists_regularization_scalar_shell
-- name    : OAI.Falconer.Regularization.exists_regularization_scalar_shell
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:45:12.27046+00:00
-- url     : https://prove2.me/theorems/9c6a44f2-08f6-4ea3-bdee-9ea6af2b1706
-- title:
--   OAI.Falconer.Regularization.exists_regularization_scalar_shell: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.Regularization.exists_regularization_scalar_shell` of [lean/OAI/MeasureTheory/Falconer/Shells/RegularizationScalarShell.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Shells/RegularizationScalarShell.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer.Regularization`, with `open Set MeasureTheory`, `open scoped ENNReal SchwartzMap ContDiff`):
--
--   ```lean
--   theorem exists_regularization_scalar_shell
--       (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
--       (m : ℕ) {χ : ℝ} (hχ : 0 < χ)
--       (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
--       (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
--       (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
--       (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
--       {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
--       (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4)
--       (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) :
--       ∃ lam σ κ β : ℝ, 0 < lam ∧ 0 < σ ∧ lam ≤ σ ∧ 0 < κ ∧ 0 < β ∧
--       ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
--         ∀ (Q₁ Q₂ : DyadicCube (m+3)), Q₁.side = 1 → Q₂.side = 1 →
--         ∀ (μ ν : Measure (Space (m+3))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
--         ∀ (B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞), 0 < t₁ → 0 < t₂ →
--         ∀ p₁ p₂ : List ℕ → CellPath (m+3),
--         (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, regularizationLabel Q₁ μ N B₁ (p₁ T) = T) →
--         (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, regularizationLabel Q₂ ν N B₂ (p₂ T) = T) →
--         (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁,
--           RegularizedProfileData Q₁ (sourceClass Q₁ μ N B₁ (p₁ T)) N ((m+3:ℕ)/2+χ) lam
--             (sourceUnitProfile Q₁ μ N B₁ (p₁ T))) →
--         (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂,
--           RegularizedProfileData Q₂ (sourceClass Q₂ ν N B₂ (p₂ T)) N ((m+3:ℕ)/2+χ) lam
--             (sourceUnitProfile Q₂ ν N B₂ (p₂ T))) →
--         (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W) →
--         (∀ᵐ z : Space (m+3) × Space (m+3) ∂μ.prod ν,
--           ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
--         ∃ c : List ℕ × List ℕ → ℕ,
--           (∀ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂), c i ≤ N) ∧
--           ∀ (k : ℕ) (A D : Fin k → Set (Space (m+3))),
--             (∀ j, MeasurableSet (A j) ∧ MeasurableSet (D j)) →
--             (Pairwise fun j l => Disjoint (A j ×ˢ D j) (A l ×ˢ D l)) →
--             PlanarFalconer.shellEnergy
--               (regularizationPairDistance Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c (⋃ j, A j ×ˢ D j)) N ≤
--                 2*(k:ℝ)^2*((2:ℝ)^N)^(-β/16)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.shellEnergy` (definitions bundle `OAIQ038F000` of this split); `OAI.Falconer.DyadicCube`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.gnomonicChart`, `OAI.Falconer.Regularization.CellPath` and `OAI.Falconer.Regularization.RegularizedProfileData` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedGnomonicSurface`, `OAI.Falconer.PublishedQuadraticStationary`, `OAI.Falconer.Regularization.regularizationIndex`, `OAI.Falconer.Regularization.regularizationLabel`, `OAI.Falconer.Regularization.regularizationPairDistance`, `OAI.Falconer.Regularization.sourceClass` and `OAI.Falconer.Regularization.sourceUnitProfile` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI.Falconer.prepared_pair_positive_distance` and `OAI_Falconer_unit_pair_positive_distance` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Shells/RegularizationScalarShell.lean (declaration OAI.Falconer.Regularization.exists_regularization_scalar_shell)

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
open scoped ENNReal SchwartzMap ContDiff

theorem exists_regularization_scalar_shell
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {χ : ℝ} (hχ : 0 < χ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) :
    ∃ lam σ κ β : ℝ, 0 < lam ∧ 0 < σ ∧ lam ≤ σ ∧ 0 < κ ∧ 0 < β ∧
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ (Q₁ Q₂ : DyadicCube (m+3)), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (μ ν : Measure (Space (m+3))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞), 0 < t₁ → 0 < t₂ →
      ∀ p₁ p₂ : List ℕ → CellPath (m+3),
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, regularizationLabel Q₁ μ N B₁ (p₁ T) = T) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, regularizationLabel Q₂ ν N B₂ (p₂ T) = T) →
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁,
        RegularizedProfileData Q₁ (sourceClass Q₁ μ N B₁ (p₁ T)) N ((m+3:ℕ)/2+χ) lam
          (sourceUnitProfile Q₁ μ N B₁ (p₁ T))) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂,
        RegularizedProfileData Q₂ (sourceClass Q₂ ν N B₂ (p₂ T)) N ((m+3:ℕ)/2+χ) lam
          (sourceUnitProfile Q₂ ν N B₂ (p₂ T))) →
      (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂μ.prod ν,
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      ∃ c : List ℕ × List ℕ → ℕ,
        (∀ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂), c i ≤ N) ∧
        ∀ (k : ℕ) (A D : Fin k → Set (Space (m+3))),
          (∀ j, MeasurableSet (A j) ∧ MeasurableSet (D j)) →
          (Pairwise fun j l => Disjoint (A j ×ˢ D j) (A l ×ˢ D l)) →
          PlanarFalconer.shellEnergy
            (regularizationPairDistance Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c (⋃ j, A j ×ˢ D j)) N ≤
              2*(k:ℝ)^2*((2:ℝ)^N)^(-β/16) := by
  sorry

end Falconer.Regularization

end OAI
end
