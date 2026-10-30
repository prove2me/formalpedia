-- Prove2me | Theorems.Thm_OAI_Falconer_exists_two_profile_masked_shell_order
-- name    : OAI.Falconer.exists_two_profile_masked_shell_order
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:51:22.345579+00:00
-- url     : https://prove2.me/theorems/6a41ec2a-7f4f-478f-8328-4b373fbc5c99
-- title:
--   OAI.Falconer.exists_two_profile_masked_shell_order: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.exists_two_profile_masked_shell_order` of [lean/OAI/MeasureTheory/Falconer/Shells/TwoProfileMaskedShell.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Shells/TwoProfileMaskedShell.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory`, `open scoped ContDiff`, `open PlanarFalconer (PolicyDescriptor)`):
--
--   ```lean
--    theorem exists_two_profile_masked_shell_order
--       (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
--       (n : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
--       ∃ k : ℕ, ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ L : ℕ,
--         ∃ A B : Fin (k+1) → ℝ, (∀ j, 1 ≤ A j) ∧ (∀ j, 1 ≤ B j) ∧
--         ∀ R E δ W C₀ : ℝ, 1 ≤ R → 1 ≤ E → E ≤ R^2 → ∀ (hδ : 0 < δ) (hW : 0 < W), 1 ≤ C₀ →
--         ∀ (Q₁ Q₂ : DyadicCube (n+3)) (ρ₁ ρ₂ : Measure (Space (n+3)))
--           (profile₁ profile₂ : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
--           (F G : Finset PolicyDescriptor) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (n+3))),
--         (∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
--         (∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
--         (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E) →
--         (∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E) →
--         ∀ (μ ν : Measure (Space (n+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--           (M P s : ℝ), 0 < M → 0 < P → 0 < s →
--         (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W) →
--         (∀ᵐ z : Space (n+3) × Space (n+3) ∂μ.prod ν,
--           ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (n+2)) : Space (n+3))‖ ≤ 1/8) →
--         (∀ x y l, l ≤ 2*(k+1)+(n+2)+1 → ∀ w : Sphere (n+3),
--           ‖iteratedFDeriv ℝ l (fun t =>
--             (descriptorAmbientProduct Q₁ ρ₁ profile₁ N σ J i F S₁ x t : ℂ)*
--             (descriptorAmbientProduct Q₂ ρ₂ profile₂ N σ J i G S₂ y t : ℂ)) w‖ ≤ C₀*E^l) →
--         ∀ U : ℝ, 0 < U → ∀ (a v : ℝ) (Ψ : ℝ → ℝ),
--         Measurable Ψ → (∀ x, 0 ≤ Ψ x) → (∀ x ≤ 0, Ψ x = 0) →
--         (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
--         ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
--         (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
--           0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a)) →
--         (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
--           ∀ᵐ z ∂μ.prod ν, 1 ≤ r*dist z.1 z.2 ∧ E^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
--         ∀ energy : ℝ,
--         (∀ (u : DescriptorJetSymbol (n+1) (2*k) L F 1)
--           (w : DescriptorJetSymbol (n+1) (2*k) L G 1),
--           independentAngularEnergy a v Ψ
--             (fun z => endpointTransform μ M (u.value Q₁ ρ₁ profile₁ N σ J i S₁ U) z.1 z.2)
--             (fun z => endpointTransform ν P (w.value Q₂ ρ₂ profile₂ N σ J i S₂ U) z.1 z.2) ≤ energy) →
--         let f := descriptorRootSymbol (n+1) F (L+2*k)
--         let g := descriptorRootSymbol (n+1) G (L+2*k)
--         let left := descriptorAmbientProduct Q₁ ρ₁ profile₁ N σ J i F S₁
--         let right := descriptorAmbientProduct Q₂ ρ₂ profile₂ N σ J i G S₂
--         (2:ℝ)^(-a) * (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)),
--           ‖charFun (endpointWeightedDistance μ ν M P s left right) r‖^2) ≤
--           2*(descriptorInverseShellCost f g k A B 1 1 U δ W hδ hW*energy)+
--           2*(2:ℝ)^(v-a)*
--             (|M⁻¹*P⁻¹| *((δ^(-(((n+2:ℕ):ℝ)/2))*A₀*C₀*R^(-T))*(μ.prod ν).real univ))^2*
--             (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PolicyDescriptor` and `OAI.PlanarFalconer.sourceAngularShellMeasure` (definitions bundle `OAIQ038F000` of this split); `OAI.Falconer.DescriptorJetSymbol`, `OAI.Falconer.DyadicCube`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.descriptorAmbientProduct`, `OAI.Falconer.descriptorMaskRadius`, `OAI.Falconer.endpointTransform`, `OAI.Falconer.endpointWeightedDistance`, `OAI.Falconer.gnomonicChart`, `OAI.Falconer.independentAngularEnergy` and `OAI.Falconer.DescriptorJetSymbol.value` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedGnomonicSurface`, `OAI.Falconer.PublishedQuadraticStationary`, `OAI.Falconer.descriptorInverseShellCost` and `OAI.Falconer.descriptorRootSymbol` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.exists_regular_class_shell` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Shells/TwoProfileMaskedShell.lean (declaration OAI.Falconer.exists_two_profile_masked_shell_order)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

 theorem exists_two_profile_masked_shell_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (n : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ k : ℕ, ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ L : ℕ,
      ∃ A B : Fin (k+1) → ℝ, (∀ j, 1 ≤ A j) ∧ (∀ j, 1 ≤ B j) ∧
      ∀ R E δ W C₀ : ℝ, 1 ≤ R → 1 ≤ E → E ≤ R^2 → ∀ (hδ : 0 < δ) (hW : 0 < W), 1 ≤ C₀ →
      ∀ (Q₁ Q₂ : DyadicCube (n+3)) (ρ₁ ρ₂ : Measure (Space (n+3)))
        (profile₁ profile₂ : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
        (F G : Finset PolicyDescriptor) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (n+3))),
      (∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E) →
      (∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E) →
      ∀ (μ ν : Measure (Space (n+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
        (M P s : ℝ), 0 < M → 0 < P → 0 < s →
      (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W) →
      (∀ᵐ z : Space (n+3) × Space (n+3) ∂μ.prod ν,
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (n+2)) : Space (n+3))‖ ≤ 1/8) →
      (∀ x y l, l ≤ 2*(k+1)+(n+2)+1 → ∀ w : Sphere (n+3),
        ‖iteratedFDeriv ℝ l (fun t =>
          (descriptorAmbientProduct Q₁ ρ₁ profile₁ N σ J i F S₁ x t : ℂ)*
          (descriptorAmbientProduct Q₂ ρ₂ profile₂ N σ J i G S₂ y t : ℂ)) w‖ ≤ C₀*E^l) →
      ∀ U : ℝ, 0 < U → ∀ (a v : ℝ) (Ψ : ℝ → ℝ),
      Measurable Ψ → (∀ x, 0 ≤ Ψ x) → (∀ x ≤ 0, Ψ x = 0) →
      (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a)) →
      (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        ∀ᵐ z ∂μ.prod ν, 1 ≤ r*dist z.1 z.2 ∧ E^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
      ∀ energy : ℝ,
      (∀ (u : DescriptorJetSymbol (n+1) (2*k) L F 1)
        (w : DescriptorJetSymbol (n+1) (2*k) L G 1),
        independentAngularEnergy a v Ψ
          (fun z => endpointTransform μ M (u.value Q₁ ρ₁ profile₁ N σ J i S₁ U) z.1 z.2)
          (fun z => endpointTransform ν P (w.value Q₂ ρ₂ profile₂ N σ J i S₂ U) z.1 z.2) ≤ energy) →
      let f := descriptorRootSymbol (n+1) F (L+2*k)
      let g := descriptorRootSymbol (n+1) G (L+2*k)
      let left := descriptorAmbientProduct Q₁ ρ₁ profile₁ N σ J i F S₁
      let right := descriptorAmbientProduct Q₂ ρ₂ profile₂ N σ J i G S₂
      (2:ℝ)^(-a) * (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)),
        ‖charFun (endpointWeightedDistance μ ν M P s left right) r‖^2) ≤
        2*(descriptorInverseShellCost f g k A B 1 1 U δ W hδ hW*energy)+
        2*(2:ℝ)^(v-a)*
          (|M⁻¹*P⁻¹| *((δ^(-(((n+2:ℕ):ℝ)/2))*A₀*C₀*R^(-T))*(μ.prod ν).real univ))^2*
          (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  sorry

end Falconer

end OAI
end
