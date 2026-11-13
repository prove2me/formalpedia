-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_linear_unperturbed_solver
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_linear_unperturbed_solver
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T10:15:27.3949+00:00
-- url     : https://prove2.me/theorems/b7b0772c-1531-43f8-8734-61730442d602
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_linear_unperturbed_solver: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_linear_unperturbed_solver` of [lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialLinearSolver.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialLinearSolver.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation`, with `open Set TopologicalSpace`, `open scoped ContDiff NNReal`, `open WeightedEstimates PhaseMean RealModes PhaseGeometry`):
--
--   ```lean
--   theorem polynomial_linear_unperturbed_solver :
--       ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
--       ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
--         {U : Set SmallModes.Base} (hU : IsOpen U)
--         {ξ : SmallModes.Base} (hξ : ξ ≠ 0)
--         {φ : Base → ℝ} (_hφ : ContDiff ℝ ∞ φ)
--         (_hphase : coordinatePhase φ = phaseLinear ξ),
--         (modeSupport K : Set SmallModes.Base) ⊆ U →
--         (∀ x ∈ U, Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
--         (∀ x ∈ U, Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x) ξ) →
--         ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
--         ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
--         (∀ m, ‖ξ‖ ≤ B m ∧ ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ B m ∧
--           (∀ j ≤ m+3, WeightedBound U 1 j (B m/(s : ℝ)^(j-2))
--             (G ∘ planeCoordinateIsometry.symm)) ∧
--           (∀ x ∈ U, ‖(NormalFrame.gramDet
--             (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
--             (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ B m) ∧
--           (∀ x ∈ U, ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
--             (-ξ.2,ξ.1)‖⁻¹ ≤ B m)) →
--         ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
--           c.e = linearPhaseChart ξ hξ U hU ∧
--           (∀ m, c.C m = A m*(B m)^(p m)) ∧
--           (∀ m, c.D m = 0) ∧ (∀ m, c.J m = 1+2*B m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet` and `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.phaseLinear`, `OAI.ClosedSurfaceR4.PhaseGeometry.Good`, `OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart`, `OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv`, `OAI.ClosedSurfaceR4.PhaseGeometry.secondQuadratic`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePhase` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.emptyMetricPolynomial` (definitions bundle `OAIQ249SI007` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_grid_mean_data` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialLinearSolver.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_linear_unperturbed_solver)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
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
open WeightedEstimates PhaseMean RealModes PhaseGeometry

theorem polynomial_linear_unperturbed_solver :
    ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
    ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
      {U : Set SmallModes.Base} (hU : IsOpen U)
      {ξ : SmallModes.Base} (hξ : ξ ≠ 0)
      {φ : Base → ℝ} (_hφ : ContDiff ℝ ∞ φ)
      (_hphase : coordinatePhase φ = phaseLinear ξ),
      (modeSupport K : Set SmallModes.Base) ⊆ U →
      (∀ x ∈ U, Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ U, Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x) ξ) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m, ‖ξ‖ ≤ B m ∧ ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ B m ∧
        (∀ j ≤ m+3, WeightedBound U 1 j (B m/(s : ℝ)^(j-2))
          (G ∘ planeCoordinateIsometry.symm)) ∧
        (∀ x ∈ U, ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ B m) ∧
        (∀ x ∈ U, ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-ξ.2,ξ.1)‖⁻¹ ≤ B m)) →
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
        c.e = linearPhaseChart ξ hξ U hU ∧
        (∀ m, c.C m = A m*(B m)^(p m)) ∧
        (∀ m, c.D m = 0) ∧ (∀ m, c.J m = 1+2*B m) := by
  sorry

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end
