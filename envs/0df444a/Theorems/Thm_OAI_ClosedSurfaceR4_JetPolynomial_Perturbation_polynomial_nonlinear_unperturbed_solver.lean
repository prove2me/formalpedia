-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_nonlinear_unperturbed_solver
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_nonlinear_unperturbed_solver
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T10:17:09.352994+00:00
-- url     : https://prove2.me/theorems/1a42202d-42ad-4c39-bd9c-17de568e9681
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_nonlinear_unperturbed_solver: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_nonlinear_unperturbed_solver` of [lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialNonlinearSolver.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialNonlinearSolver.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation`, with `open Set TopologicalSpace`, `open scoped ContDiff NNReal`, `open WeightedEstimates PhaseMean RealModes PhaseGeometry`):
--
--   ```lean
--   theorem polynomial_nonlinear_unperturbed_solver :
--       ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
--       ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
--         {φ : Base → ℝ} (_hφ : ContDiff ℝ ∞ φ)
--         (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
--         (_he : ContDiff ℝ ∞ e) (_hi : ContDiff ℝ ∞ e.symm),
--         (∀ x, (e x).1 = coordinatePhase φ x) →
--         (modeSupport K : Set SmallModes.Base) ⊆ e.source →
--         (∀ x ∈ e.source, Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
--         (∀ x ∈ e.source, Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
--           (phaseDerivative (coordinatePhase φ) x)) →
--         ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
--         ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
--         (∀ m,
--           (∀ j ≤ m+3, WeightedBound e.source 1 j (B m/(s : ℝ)^(j-2))
--             (G ∘ planeCoordinateIsometry.symm)) ∧
--           (∀ j, 1 ≤ j → j ≤ m+3 → ∀ x ∈ e.source,
--             ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B m) ∧
--           (∀ x ∈ e.source, ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ B m) ∧
--           (∀ x ∈ e.source, |coordDet (fderiv ℝ e x)| ≤ B m) ∧
--           (∀ x ∈ e.source, ‖(NormalFrame.gramDet
--             (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
--             (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ B m) ∧
--           (∀ x ∈ e.source, ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
--             (-(phaseDerivative (coordinatePhase φ) x).2,
--               (phaseDerivative (coordinatePhase φ) x).1)‖⁻¹ ≤ B m)) →
--         ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
--           c.e = e ∧ (∀ m, c.C m = A m*(B m)^(p m)) ∧
--           (∀ m, c.D m = 0) ∧ (∀ m, c.J m = B m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet` and `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.phaseDerivative`, `OAI.ClosedSurfaceR4.PhaseGeometry.Good`, `OAI.ClosedSurfaceR4.PhaseGeometry.secondQuadratic`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePhase` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.RealModes.coordDet` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.emptyMetricPolynomial` (definitions bundle `OAIQ249SI007` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.PhaseGeometry.finite_catalog_polynomial_cancellation` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialNonlinearSolver.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_nonlinear_unperturbed_solver)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
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

theorem polynomial_nonlinear_unperturbed_solver :
    ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
    ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
      {φ : Base → ℝ} (_hφ : ContDiff ℝ ∞ φ)
      (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
      (_he : ContDiff ℝ ∞ e) (_hi : ContDiff ℝ ∞ e.symm),
      (∀ x, (e x).1 = coordinatePhase φ x) →
      (modeSupport K : Set SmallModes.Base) ⊆ e.source →
      (∀ x ∈ e.source, Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ e.source, Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
        (phaseDerivative (coordinatePhase φ) x)) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m,
        (∀ j ≤ m+3, WeightedBound e.source 1 j (B m/(s : ℝ)^(j-2))
          (G ∘ planeCoordinateIsometry.symm)) ∧
        (∀ j, 1 ≤ j → j ≤ m+3 → ∀ x ∈ e.source,
          ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B m) ∧
        (∀ x ∈ e.source, ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ B m) ∧
        (∀ x ∈ e.source, |coordDet (fderiv ℝ e x)| ≤ B m) ∧
        (∀ x ∈ e.source, ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ B m) ∧
        (∀ x ∈ e.source, ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-(phaseDerivative (coordinatePhase φ) x).2,
            (phaseDerivative (coordinatePhase φ) x).1)‖⁻¹ ≤ B m)) →
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
        c.e = e ∧ (∀ m, c.C m = A m*(B m)^(p m)) ∧
        (∀ m, c.D m = 0) ∧ (∀ m, c.J m = B m) := by
  sorry

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end
