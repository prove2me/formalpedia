-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_linear_perturbed_mean_family_all_profiles
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_linear_perturbed_mean_family_all_profiles
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T09:53:52.901669+00:00
-- url     : https://prove2.me/theorems/eccf7084-a7ca-4f59-bd6c-eb28d7e86032
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_linear_perturbed_mean_family_all_profiles (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_linear_perturbed_mean_family_all_profiles` of [lean/OAI/Geometry/SurfaceImmersion/Correction/UniformLinearPerturbedMeanFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/UniformLinearPerturbedMeanFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation`, with `open Set TopologicalSpace`, `open scoped ContDiff NNReal`, `open WeightedEstimates RealModes PhaseMean PhaseGeometry`):
--
--   ```lean
--   theorem uniform_linear_perturbed_mean_family_all_profiles {n : ℕ}
--       (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
--       {F : Base → Space} (hF : ContDiff ℝ ∞ F)
--       (Ω U K : Fin 3 → Set SmallModes.Base)
--       (hΩ : ∀ j, IsOpen (Ω j)) (hU : ∀ j, IsOpen (U j))
--       (hK : ∀ j, IsCompact (K j)) (hUK : ∀ j, U j ⊆ K j) (hKΩ : ∀ j, K j ⊆ Ω j)
--       (ξ : Fin 3 → SmallModes.Base) (hξ : ∀ j, ξ j ≠ 0)
--       (hImm : ∀ j x, x ∈ Ω j → Function.Injective
--         (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) x))
--       (hgood : ∀ j x, x ∈ Ω j →
--         Good (realSecondTensor (F ∘ planeCoordinateIsometry.symm) x) (ξ j))
--       (S : Fin 3 → Compacts Base)
--       (hS : ∀ j, (modeSupport (S j) : Set SmallModes.Base) ⊆ U j)
--       {U₀ : Set Base} (hU₀ : IsOpen U₀) (K₀ : Compacts Base)
--       (hU₀K : U₀ ⊆ K₀) (hSU₀ : ∀ j, (S j : Set Base) ⊆ U₀)
--       (φ : Fin 3 → Base → ℝ) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
--       (hphase : ∀ j, coordinatePhase (φ j) = phaseLinear (ξ j))
--       (ψ : ∀ j, SupportedField (F := ℝ)
--         (chartSupport (linearPhaseChart (ξ j) (hξ j) (U j) (hU j))
--           (modeSupport (S j)) (hS j)))
--       (Q : Fin 3 → Tensor →L[ℝ] ℝ) {r ρ R : ℝ}
--       {reference : SmallModes.Base → Tensor}
--       (hmargin : ∀ j x, x ∈ U j → ρ + ‖Q j‖ * r ≤ Q j (reference x) ∧
--         Q j (reference x) ≤ R - ‖Q j‖ * r) :
--       ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (H : Fin 3 → ℕ → ℝ) (Pjet : ℕ → ℝ),
--         (∀ j m, 1 ≤ H j m) → (∀ m, 0 ≤ Pjet m) →
--         ∃ p : Fin 3 → ChartedMeanProfile P,
--           (∀ j, (p j).U = U₀) ∧ (∀ j, (p j).O = univ) ∧
--           (∀ j m, 0 ≤ (p j).D m) ∧
--         ∀ (G : Base → Space) (_hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
--         0 ≤ C₀ → C₀ < ρ₀ →
--         WeightedBound univ 1 2 C₀
--           ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
--         ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
--         (∀ j m, WeightedBound (linearPhaseChart (ξ j) (hξ j) (U j) (hU j)).target
--           s m (H j m) (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
--             (linearPhaseChart (ξ j) (hξ j) (U j) (hU j)).symm))) →
--         (∀ m j, j ≤ m + 2 → WeightedBound U₀ 1 j
--           (Pjet m / (s : ℝ) ^ (j - 2)) G) →
--         ∀ (τ ε r' : ℝ), r' ≤ r → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
--         ∃ d : ChartedMeanFamilyData P ε τ s r' ρ R reference,
--           d.Fits p ∧ d.G = G ∧ d.phase = φ ∧ d.support = S ∧
--           (∀ j, (d.solver j).e = linearPhaseChart (ξ j) (hξ j) (U j) (hU j)) ∧
--           (∀ j x, (d.data j).cutoff x = ψ j x) ∧
--           (∀ j, (d.data j).form = fun _ => Q j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.JetPolynomial.chartSupport`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.phaseLinear`, `OAI.ClosedSurfaceR4.PhaseGeometry.Good`, `OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.RealTwoJet`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.RealModes.realTwoJet`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePhase`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanProfile`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData.Fits` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.chartCompact` (definitions bundle `OAIQ249SI007` of this split).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_small_increment` and `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_polynomial_atlas_small_increment` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/UniformLinearPerturbedMeanFamily.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_linear_perturbed_mean_family_all_profiles)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseMean PhaseGeometry

theorem uniform_linear_perturbed_mean_family_all_profiles {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    {F : Base → Space} (hF : ContDiff ℝ ∞ F)
    (Ω U K : Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ j, IsOpen (Ω j)) (hU : ∀ j, IsOpen (U j))
    (hK : ∀ j, IsCompact (K j)) (hUK : ∀ j, U j ⊆ K j) (hKΩ : ∀ j, K j ⊆ Ω j)
    (ξ : Fin 3 → SmallModes.Base) (hξ : ∀ j, ξ j ≠ 0)
    (hImm : ∀ j x, x ∈ Ω j → Function.Injective
      (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) x))
    (hgood : ∀ j x, x ∈ Ω j →
      Good (realSecondTensor (F ∘ planeCoordinateIsometry.symm) x) (ξ j))
    (S : Fin 3 → Compacts Base)
    (hS : ∀ j, (modeSupport (S j) : Set SmallModes.Base) ⊆ U j)
    {U₀ : Set Base} (hU₀ : IsOpen U₀) (K₀ : Compacts Base)
    (hU₀K : U₀ ⊆ K₀) (hSU₀ : ∀ j, (S j : Set Base) ⊆ U₀)
    (φ : Fin 3 → Base → ℝ) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hphase : ∀ j, coordinatePhase (φ j) = phaseLinear (ξ j))
    (ψ : ∀ j, SupportedField (F := ℝ)
      (chartSupport (linearPhaseChart (ξ j) (hξ j) (U j) (hU j))
        (modeSupport (S j)) (hS j)))
    (Q : Fin 3 → Tensor →L[ℝ] ℝ) {r ρ R : ℝ}
    {reference : SmallModes.Base → Tensor}
    (hmargin : ∀ j x, x ∈ U j → ρ + ‖Q j‖ * r ≤ Q j (reference x) ∧
      Q j (reference x) ≤ R - ‖Q j‖ * r) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (H : Fin 3 → ℕ → ℝ) (Pjet : ℕ → ℝ),
      (∀ j m, 1 ≤ H j m) → (∀ m, 0 ≤ Pjet m) →
      ∃ p : Fin 3 → ChartedMeanProfile P,
        (∀ j, (p j).U = U₀) ∧ (∀ j, (p j).O = univ) ∧
        (∀ j m, 0 ≤ (p j).D m) ∧
      ∀ (G : Base → Space) (_hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
      0 ≤ C₀ → C₀ < ρ₀ →
      WeightedBound univ 1 2 C₀
        ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
      ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
      (∀ j m, WeightedBound (linearPhaseChart (ξ j) (hξ j) (U j) (hU j)).target
        s m (H j m) (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
          (linearPhaseChart (ξ j) (hξ j) (U j) (hU j)).symm))) →
      (∀ m j, j ≤ m + 2 → WeightedBound U₀ 1 j
        (Pjet m / (s : ℝ) ^ (j - 2)) G) →
      ∀ (τ ε r' : ℝ), r' ≤ r → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      ∃ d : ChartedMeanFamilyData P ε τ s r' ρ R reference,
        d.Fits p ∧ d.G = G ∧ d.phase = φ ∧ d.support = S ∧
        (∀ j, (d.solver j).e = linearPhaseChart (ξ j) (hξ j) (U j) (hU j)) ∧
        (∀ j x, (d.data j).cutoff x = ψ j x) ∧
        (∀ j, (d.data j).form = fun _ => Q j) := by
  sorry

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end
