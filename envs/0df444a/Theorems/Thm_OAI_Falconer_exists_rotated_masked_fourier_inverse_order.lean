-- Prove2me | Theorems.Thm_OAI_Falconer_exists_rotated_masked_fourier_inverse_order
-- name    : OAI.Falconer.exists_rotated_masked_fourier_inverse_order
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:50:28.967837+00:00
-- url     : https://prove2.me/theorems/a668e9e1-1972-4107-892a-49291c82098b
-- title:
--   OAI.Falconer.exists_rotated_masked_fourier_inverse_order: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.exists_rotated_masked_fourier_inverse_order` of [lean/OAI/MeasureTheory/Falconer/Estimates/RotatedMaskedRemainder.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/RotatedMaskedRemainder.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory`, `open scoped ContDiff`):
--
--   ```lean
--   theorem exists_rotated_masked_fourier_inverse_order
--       (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
--       (n : ℕ) {κ Z : ℝ} (hκ : 0 < κ) :
--       ∃ K : ℕ, ∃ A : ℝ, 0 ≤ A ∧
--         ∀ (T : Space (n+3) ≃ₗᵢ[ℝ] Space (n+3)), ∀ R D r δ : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 → 0 < δ →
--         ∀ (w₀ : Sphere (n+3)) (Q : DyadicCube (n+3)) (ρ : Measure (Space (n+3)))
--           [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
--           (B : Finset PlanarFalconer.PolicyDescriptor)
--           (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+3)))
--           (X Y : DyadicCube (n+3)),
--         (∀ b ∈ B, ∀ w : Sphere (n+3), ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
--         (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
--           δ ≤ dist z.1 z.2*(2:ℝ)^a) →
--         (∀ᵐ z : Space (n+3) × Space (n+3) ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
--           ‖T (NormedSpace.normalize (z.1-z.2))-(gnomonicChart (0 : Space (n+2)) : Space (n+3))‖ ≤ 1/8) →
--         (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
--           1 ≤ r*dist z.1 z.2 ∧ D^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
--         ∀ C : ℝ, 1 ≤ C →
--         (∀ x y k, k ≤ 2*(K+1)+(n+2)+1 → ∀ w : Sphere (n+3),
--           ‖iteratedFDeriv ℝ k (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S x y) w‖ ≤ C*D^k) →
--         Integrable (fun z : Space (n+3) × Space (n+3) =>
--           rotatedScaledWeightedInverseSum n K T ((2:ℝ)^a)⁻¹ r (z.1-z.2)
--             (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S z.1 z.2))
--           ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)) →
--         ‖((profileModelMass m N a)⁻¹*(profileModelMass m N a)⁻¹) •
--             (∫ z : Space (n+3) × Space (n+3),
--               rotatedScaledWeightedInverseSum n K T ((2:ℝ)^a)⁻¹ r (z.1-z.2)
--                 (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S z.1 z.2)
--               ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)) -
--           charFun (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) r‖ ≤
--         |(profileModelMass m N a)⁻¹*(profileModelMass m N a)⁻¹| *
--           ((δ^(-(((n+2:ℕ):ℝ)/2))*A*C*R^(-Z))*
--             ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)).real univ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PolicyDescriptor` (definitions bundle `OAIQ038F000` of this split); `OAI.Falconer.DyadicCube`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.descriptorMaskRadius`, `OAI.Falconer.gnomonicChart`, `OAI.Falconer.maskedCellDistance`, `OAI.Falconer.profileModelMass` and `OAI.Falconer.DyadicCube.carrier` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedGnomonicSurface`, `OAI.Falconer.PublishedQuadraticStationary`, `OAI.Falconer.descriptorPairAmplitude` and `OAI.Falconer.rotatedScaledWeightedInverseSum` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI.Falconer.exists_policy_scalar_conversion` and `OAI_Falconer_exists_rotated_masked_jet_shell_order` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/RotatedMaskedRemainder.lean (declaration OAI.Falconer.exists_rotated_masked_fourier_inverse_order)

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

theorem exists_rotated_masked_fourier_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (n : ℕ) {κ Z : ℝ} (hκ : 0 < κ) :
    ∃ K : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ (T : Space (n+3) ≃ₗᵢ[ℝ] Space (n+3)), ∀ R D r δ : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 → 0 < δ →
      ∀ (w₀ : Sphere (n+3)) (Q : DyadicCube (n+3)) (ρ : Measure (Space (n+3)))
        [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
        (B : Finset PlanarFalconer.PolicyDescriptor)
        (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+3)))
        (X Y : DyadicCube (n+3)),
      (∀ b ∈ B, ∀ w : Sphere (n+3), ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        δ ≤ dist z.1 z.2*(2:ℝ)^a) →
      (∀ᵐ z : Space (n+3) × Space (n+3) ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        ‖T (NormedSpace.normalize (z.1-z.2))-(gnomonicChart (0 : Space (n+2)) : Space (n+3))‖ ≤ 1/8) →
      (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        1 ≤ r*dist z.1 z.2 ∧ D^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
      ∀ C : ℝ, 1 ≤ C →
      (∀ x y k, k ≤ 2*(K+1)+(n+2)+1 → ∀ w : Sphere (n+3),
        ‖iteratedFDeriv ℝ k (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S x y) w‖ ≤ C*D^k) →
      Integrable (fun z : Space (n+3) × Space (n+3) =>
        rotatedScaledWeightedInverseSum n K T ((2:ℝ)^a)⁻¹ r (z.1-z.2)
          (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S z.1 z.2))
        ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)) →
      ‖((profileModelMass m N a)⁻¹*(profileModelMass m N a)⁻¹) •
          (∫ z : Space (n+3) × Space (n+3),
            rotatedScaledWeightedInverseSum n K T ((2:ℝ)^a)⁻¹ r (z.1-z.2)
              (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S z.1 z.2)
            ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)) -
        charFun (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) r‖ ≤
      |(profileModelMass m N a)⁻¹*(profileModelMass m N a)⁻¹| *
        ((δ^(-(((n+2:ℕ):ℝ)/2))*A*C*R^(-Z))*
          ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)).real univ) := by
  sorry

end Falconer

end OAI
end
