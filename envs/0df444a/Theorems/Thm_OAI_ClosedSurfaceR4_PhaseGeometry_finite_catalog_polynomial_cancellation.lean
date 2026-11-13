-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_PhaseGeometry_finite_catalog_polynomial_cancellation
-- name    : OAI.ClosedSurfaceR4.PhaseGeometry.finite_catalog_polynomial_cancellation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T09:53:58.447307+00:00
-- url     : https://prove2.me/theorems/7b425196-d57c-43d7-b95f-b3b6be0e90e6
-- title:
--   OAI.ClosedSurfaceR4.PhaseGeometry.finite_catalog_polynomial_cancellation: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.PhaseGeometry.finite_catalog_polynomial_cancellation` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/FiniteCatalogCancellation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/FiniteCatalogCancellation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.PhaseGeometry`, with `open Set TopologicalSpace`, `open scoped ContDiff BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates RealModes`):
--
--   ```lean
--   theorem finite_catalog_polynomial_cancellation
--       (Γ : Finset (SmallModes.Base → ℝ)) (hΓ : ∀ φ ∈ Γ, ContDiff ℝ ∞ φ)
--       (K₀ : Compacts SmallModes.Base) {ε b D : ℝ}
--       (hε : 0 < ε) (hb : 0 < b) (hD : 1 ≤ D) (hDB : (ε*b)⁻¹ ≤ D)
--       (B : ℕ → ℝ → ℝ) (hB : ∀ m, HasPolynomialBound (B m))
--       (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
--       ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
--         ∀ x : ℝ, 1 ≤ x → ∀ φ ∈ Γ,
--         ∀ {G : JetPolynomial.Base → JetPolynomial.Space} (_hG : ContDiff ℝ ∞ G)
--           (K : Compacts SmallModes.Base), (K : Set SmallModes.Base) ⊆ K₀ →
--         (∀ y ∈ (K : Set SmallModes.Base),
--           Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) y)) →
--         (∀ y ∈ (K : Set SmallModes.Base), b ≤ ‖realSecondTensor (G ∘ planeCoordinateIsometry.symm) y‖) →
--         (∀ y ∈ (K : Set SmallModes.Base),
--           ε*‖realSecondTensor (G ∘ planeCoordinateIsometry.symm) y‖ ≤
--             ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) y)
--               (-(phaseDerivative φ y).2,(phaseDerivative φ y).1)‖) →
--         (∀ y ∈ (K : Set SmallModes.Base),
--           ‖(NormalFrame.gramDet
--             (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) y)
--             (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) y))⁻¹‖ ≤ D) →
--         ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
--         (∀ m j, j ≤ m+3 → WeightedBound univ 1 j
--           (B m x/(s : ℝ)^(j-2)) (G ∘ planeCoordinateIsometry.symm)) →
--         ∀ f : SupportedField (F := ComplexTensor) K,
--         ∃ X : RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
--           (∀ m, WeightedBound univ τ m
--             (E m*x^(d m)*supportedWeightedSeminorm K s
--               (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f) X) ∧
--           (∀ m, WeightedBound univ τ m
--             ((τ/s)^(q+1)*(E m*x^(d m))*supportedWeightedSeminorm K s
--               (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f)
--             (realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
--               QuadraticMean.displacement τ φ f))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.JetPolynomial.supportedWeightedSeminorm`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.PhaseMean.ComplexTensor`, `OAI.ClosedSurfaceR4.QuadraticMean.RVec` and `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.QuadraticMean.Base` and `OAI.ClosedSurfaceR4.RealModes.HasPolynomialBound` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.phaseDerivative`, `OAI.ClosedSurfaceR4.PhaseGeometry.secondQuadratic`, `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx` and `OAI.ClosedSurfaceR4.SmallModes.dy` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.QuadraticMean.displacement` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.inputOrder` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.RealModes.realLinearizedTensor` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.emptyMetricPolynomial` (definitions bundle `OAIQ249SI007` of this split).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_catalog_global_quadratic_correction` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_catalog_atlas_cancellation` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/FiniteCatalogCancellation.lean (declaration OAI.ClosedSurfaceR4.PhaseGeometry.finite_catalog_polynomial_cancellation)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
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
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates RealModes

theorem finite_catalog_polynomial_cancellation
    (Γ : Finset (SmallModes.Base → ℝ)) (hΓ : ∀ φ ∈ Γ, ContDiff ℝ ∞ φ)
    (K₀ : Compacts SmallModes.Base) {ε b D : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hD : 1 ≤ D) (hDB : (ε*b)⁻¹ ≤ D)
    (B : ℕ → ℝ → ℝ) (hB : ∀ m, HasPolynomialBound (B m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
    ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
      ∀ x : ℝ, 1 ≤ x → ∀ φ ∈ Γ,
      ∀ {G : JetPolynomial.Base → JetPolynomial.Space} (_hG : ContDiff ℝ ∞ G)
        (K : Compacts SmallModes.Base), (K : Set SmallModes.Base) ⊆ K₀ →
      (∀ y ∈ (K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) y)) →
      (∀ y ∈ (K : Set SmallModes.Base), b ≤ ‖realSecondTensor (G ∘ planeCoordinateIsometry.symm) y‖) →
      (∀ y ∈ (K : Set SmallModes.Base),
        ε*‖realSecondTensor (G ∘ planeCoordinateIsometry.symm) y‖ ≤
          ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) y)
            (-(phaseDerivative φ y).2,(phaseDerivative φ y).1)‖) →
      (∀ y ∈ (K : Set SmallModes.Base),
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) y)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) y))⁻¹‖ ≤ D) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m j, j ≤ m+3 → WeightedBound univ 1 j
        (B m x/(s : ℝ)^(j-2)) (G ∘ planeCoordinateIsometry.symm)) →
      ∀ f : SupportedField (F := ComplexTensor) K,
      ∃ X : RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m
          (E m*x^(d m)*supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f) X) ∧
        (∀ m, WeightedBound univ τ m
          ((τ/s)^(q+1)*(E m*x^(d m))*supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f)
          (realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ φ f)) := by
  sorry

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end
