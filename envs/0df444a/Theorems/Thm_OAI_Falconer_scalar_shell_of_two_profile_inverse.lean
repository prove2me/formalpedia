-- Prove2me | Theorems.Thm_OAI_Falconer_scalar_shell_of_two_profile_inverse
-- name    : OAI.Falconer.scalar_shell_of_two_profile_inverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:53:02.163356+00:00
-- url     : https://prove2.me/theorems/43537e7f-a56c-461a-8aae-80c869254bca
-- title:
--   OAI.Falconer.scalar_shell_of_two_profile_inverse: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.scalar_shell_of_two_profile_inverse` of [lean/OAI/MeasureTheory/Falconer/Recursion/TwoProfileInverseScalar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Recursion/TwoProfileInverseScalar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory`, `open PlanarFalconer (PolicyDescriptor)`):
--
--   ```lean
--   theorem scalar_shell_of_two_profile_inverse {m K L : ℕ}
--       {F G : Finset PolicyDescriptor} {D : ℝ}
--       {f : DescriptorJetSymbol (m+1) K L F D}
--       {g : DescriptorJetSymbol (m+1) K L G D}
--       (k R : ℕ) (A B : Fin (k+1) → ℝ)
--       (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
--       (hD : 0 < D) (hA : ∀ j, 0 < A j) (hB : ∀ j, 0 < B j)
--       (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
--       (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
--       (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
--       (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
--       (Af Ag : ℝ) {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E) (hDE : D ≤ E)
--       (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
--       (hGE : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
--       (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
--       {s : ℝ} (hs : 0 < s) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--       (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
--       {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
--       (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
--       (hzero : ∀ x ≤ 0, Ψ x = 0) (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
--       [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
--       (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
--         0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a))
--       (energy : ℝ)
--       (henergy : ∀ (u : DescriptorJetSymbol (m+1) (K+2*k) R F D)
--         (w : DescriptorJetSymbol (m+1) (K+2*k) R G D),
--         independentAngularEnergy a v Ψ
--           (fun z => endpointTransform μ M (u.value Q₁ ρ₁ profile₁ N σ J i S₁ U) z.1 z.2)
--           (fun z => endpointTransform ν P (w.value Q₂ ρ₂ profile₂ N σ J i S₂ U) z.1 z.2) ≤ energy)
--       (H : ℝ → ℂ) (hH : Measurable H) {ε : ℝ}
--       (herr : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
--         ‖H r-(M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
--           scaledWeightedInverseSum m k s r (z.1-z.2)
--             (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
--               g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) ∂μ.prod ν)‖ ≤ ε) :
--       IntegrableOn (fun r => ‖H r‖^2) (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
--         (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖H r‖^2) ≤
--           2*(descriptorInverseShellCost f g k A B Af Ag U δ W hδ hW *
--             energy) +
--           2*(2:ℝ)^(v-a)*ε^2*(PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PolicyDescriptor` and `OAI.PlanarFalconer.sourceAngularShellMeasure` (definitions bundle `OAIQ038F000` of this split); `OAI.Falconer.DescriptorInverseSymbols`, `OAI.Falconer.DescriptorJetSymbol`, `OAI.Falconer.DyadicCube`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.descriptorMaskRadius`, `OAI.Falconer.endpointTransform`, `OAI.Falconer.independentAngularEnergy`, `OAI.Falconer.DescriptorJetSymbol.ambient` and `OAI.Falconer.DescriptorJetSymbol.value` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.descriptorInverseShellCost` and `OAI.Falconer.scaledWeightedInverseSum` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.exists_two_profile_masked_shell_order` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Recursion/TwoProfileInverseScalar.lean (declaration OAI.Falconer.scalar_shell_of_two_profile_inverse)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem scalar_shell_of_two_profile_inverse {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D}
    (k R : ℕ) (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (hD : 0 < D) (hA : ∀ j, 0 < A j) (hB : ∀ j, 0 < B j)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U E : ℝ} (hU : 0 < U) (hE : 1 ≤ E) (hDE : D ≤ E)
    (hFE : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hGE : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    {s : ℝ} (hs : 0 < s) (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hzero : ∀ x ≤ 0, Ψ x = 0) (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a))
    (energy : ℝ)
    (henergy : ∀ (u : DescriptorJetSymbol (m+1) (K+2*k) R F D)
      (w : DescriptorJetSymbol (m+1) (K+2*k) R G D),
      independentAngularEnergy a v Ψ
        (fun z => endpointTransform μ M (u.value Q₁ ρ₁ profile₁ N σ J i S₁ U) z.1 z.2)
        (fun z => endpointTransform ν P (w.value Q₂ ρ₂ profile₂ N σ J i S₂ U) z.1 z.2) ≤ energy)
    (H : ℝ → ℂ) (hH : Measurable H) {ε : ℝ}
    (herr : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖H r-(M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
        scaledWeightedInverseSum m k s r (z.1-z.2)
          (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
            g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) ∂μ.prod ν)‖ ≤ ε) :
    IntegrableOn (fun r => ‖H r‖^2) (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖H r‖^2) ≤
        2*(descriptorInverseShellCost f g k A B Af Ag U δ W hδ hW *
          energy) +
        2*(2:ℝ)^(v-a)*ε^2*(PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  sorry

end Falconer

end OAI
end
