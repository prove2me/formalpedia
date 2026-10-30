-- Prove2me | Theorems.Thm_OAI_Falconer_exists_regular_class_shell
-- name    : OAI.Falconer.exists_regular_class_shell
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:50:42.637911+00:00
-- url     : https://prove2.me/theorems/0a4990a6-e815-49eb-b6bf-6acd18103bb1
-- title:
--   OAI.Falconer.exists_regular_class_shell: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.exists_regular_class_shell` of [lean/OAI/MeasureTheory/Falconer/Shells/RegularClassShell.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Shells/RegularClassShell.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory`, `open scoped SchwartzMap ContDiff`):
--
--   ```lean
--    theorem exists_regular_class_shell
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
--         ∀ (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ),
--         Regularization.RegularizedProfileData Q₁ ρ₁ N ((m+3:ℕ)/2+χ) lam profile₁ →
--         Regularization.RegularizedProfileData Q₂ ρ₂ N ((m+3:ℕ)/2+χ) lam profile₂ →
--         ρ₁ Q₁.carrierᶜ = 0 → ρ₂ Q₂.carrierᶜ = 0 →
--         (∀ᵐ z ∂ρ₁.prod ρ₂, δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W) →
--         (∀ᵐ z : Space (m+3) × Space (m+3) ∂ρ₁.prod ρ₂,
--           ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
--         ∃ c : ℕ, 4*c ≤ N ∧ c+100*PlanarFalconer.sourcePolicyBlock N κ < N ∧
--           β*N/(2*(m+3:ℕ)) ≤ (c:ℝ) ∧
--         ∀ A₁ A₂ : Set (Space (m+3)), MeasurableSet A₁ → MeasurableSet A₂ →
--         (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)),
--           ‖charFun (endpointWeightedDistance (ρ₁.restrict A₁) (ρ₂.restrict A₂) 1 1 1
--             (descriptorAmbientProduct Q₁ ρ₁ (fun u => profile₁ (u/N)) N σ
--               (PlanarFalconer.sourceSmoothingLevels σ κ) 0 (regularOuterList (d := m+3) profile₁ N κ c)
--               (descriptorNets (m+3) N σ))
--             (descriptorAmbientProduct Q₂ ρ₂ (fun u => profile₂ (u/N)) N σ
--               (PlanarFalconer.sourceSmoothingLevels σ κ) 0 (regularOuterList (d := m+3) profile₂ N κ c)
--               (descriptorNets (m+3) N σ))) r‖^2) ≤ ((2:ℝ)^N)^(-β/16)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.sourcePolicyBlock` and `OAI.PlanarFalconer.sourceSmoothingLevels` (definitions bundle `OAIQ038F000` of this split); `OAI.Falconer.DyadicCube`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.descriptorAmbientProduct`, `OAI.Falconer.endpointWeightedDistance`, `OAI.Falconer.gnomonicChart`, `OAI.Falconer.DyadicCube.carrier` and `OAI.Falconer.Regularization.RegularizedProfileData` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedGnomonicSurface`, `OAI.Falconer.PublishedQuadraticStationary`, `OAI.Falconer.descriptorNets` and `OAI.Falconer.regularOuterList` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.Regularization.exists_regularization_scalar_shell` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Shells/RegularClassShell.lean (declaration OAI.Falconer.exists_regular_class_shell)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff

 theorem exists_regular_class_shell
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
      ∀ (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ),
      Regularization.RegularizedProfileData Q₁ ρ₁ N ((m+3:ℕ)/2+χ) lam profile₁ →
      Regularization.RegularizedProfileData Q₂ ρ₂ N ((m+3:ℕ)/2+χ) lam profile₂ →
      ρ₁ Q₁.carrierᶜ = 0 → ρ₂ Q₂.carrierᶜ = 0 →
      (∀ᵐ z ∂ρ₁.prod ρ₂, δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂ρ₁.prod ρ₂,
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      ∃ c : ℕ, 4*c ≤ N ∧ c+100*PlanarFalconer.sourcePolicyBlock N κ < N ∧
        β*N/(2*(m+3:ℕ)) ≤ (c:ℝ) ∧
      ∀ A₁ A₂ : Set (Space (m+3)), MeasurableSet A₁ → MeasurableSet A₂ →
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)),
        ‖charFun (endpointWeightedDistance (ρ₁.restrict A₁) (ρ₂.restrict A₂) 1 1 1
          (descriptorAmbientProduct Q₁ ρ₁ (fun u => profile₁ (u/N)) N σ
            (PlanarFalconer.sourceSmoothingLevels σ κ) 0 (regularOuterList (d := m+3) profile₁ N κ c)
            (descriptorNets (m+3) N σ))
          (descriptorAmbientProduct Q₂ ρ₂ (fun u => profile₂ (u/N)) N σ
            (PlanarFalconer.sourceSmoothingLevels σ κ) 0 (regularOuterList (d := m+3) profile₂ N κ c)
            (descriptorNets (m+3) N σ))) r‖^2) ≤ ((2:ℝ)^N)^(-β/16) := by
  sorry

end Falconer

end OAI
end
