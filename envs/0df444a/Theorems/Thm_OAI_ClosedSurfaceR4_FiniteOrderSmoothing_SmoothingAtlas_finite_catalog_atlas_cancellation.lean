-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_catalog_atlas_cancellation
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_catalog_atlas_cancellation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:52:20.528336+00:00
-- url     : https://prove2.me/theorems/8e007866-358b-4980-9729-0481636754a2
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_catalog_atlas_cancellation: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_catalog_atlas_cancellation` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/AtlasCatalogCancellation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/AtlasCatalogCancellation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean`):
--
--   ```lean
--   theorem finite_catalog_atlas_cancellation
--       (Γ : A.centers → Finset (SmallModes.Base → ℝ))
--       (hΓ : ∀ i φ, φ ∈ Γ i → ContDiff ℝ ∞ φ)
--       {ε b D : ℝ} (hε : 0 < ε) (hb : 0 < b) (hD : 1 ≤ D) (hDB : (ε*b)⁻¹ ≤ D)
--       (B : ℕ → ℝ → ℝ) (hB : ∀ m, RealModes.HasPolynomialBound (B m))
--       (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
--       ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
--         ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)],
--         ∀ x : ℝ, 1 ≤ x →
--         ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F)
--           (φ : (i : A.centers) → ι i → SmallModes.Base → ℝ),
--         (∀ i j, φ i j ∈ Γ i) →
--         ∀ K : (i : A.centers) → ι i → TopologicalSpace.Compacts SmallModes.Base,
--         (∀ i j, (K i j : Set SmallModes.Base) ⊆
--           (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
--         (∀ i j y, y ∈ (K i j : Set SmallModes.Base) →
--           Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) y)) →
--         (∀ i j y, y ∈ (K i j : Set SmallModes.Base) →
--           b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y‖) →
--         (∀ i j y, y ∈ (K i j : Set SmallModes.Base) →
--           ε*‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y‖ ≤
--             ‖PhaseGeometry.secondQuadratic
--               (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
--               (-(phaseDerivative (φ i j) y).2,(phaseDerivative (φ i j) y).1)‖) →
--         (∀ i j y, y ∈ (K i j : Set SmallModes.Base) →
--           ‖(NormalFrame.gramDet
--             (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
--             (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i F) y))⁻¹‖ ≤ D) →
--         ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
--         (∀ i m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
--           (B m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
--         ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (K i j),
--         ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
--           (∀ m, A.WeightedBound τ m
--             (E m*x^(d m)*(∑ i : A.centers, ∑ j, supportedWeightedSeminorm (K i j) s
--               (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j))) W) ∧
--           (∀ m, A.TensorWeightedBound τ m
--             ((τ/s)^(q+1)*(E m*x^(d m))*(∑ i : A.centers, ∑ j,
--               supportedWeightedSeminorm (K i j) s
--                 (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j)))
--             (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
--               A.tensorPlaneRestore (fun i y => ∑ j,
--                 QuadraticMean.displacement τ (φ i j) (target i j) y)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.JetPolynomial.supportedWeightedSeminorm`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.PhaseMean.ComplexTensor`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.HasPolynomialBound` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.phaseDerivative`, `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.PhaseGeometry.secondQuadratic`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.QuadraticMean.displacement` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.inputOrder` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearMetricTensor` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.emptyMetricPolynomial` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.catalogAtlasCancellationDualAdd` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_global_quadratic_correction` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/AtlasCatalogCancellation.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_catalog_atlas_cancellation)

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
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI006
import Definitions.Def_OAIQ249SI007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.catalogAtlasCancellationDualAdd
local instance catalogAtlasCancellationFiberNormed_rb3c04b_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance catalogAtlasCancellationFiberSpace_rb3c04b_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance catalogAtlasCancellationDualSmul_rb3c04b_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance catalogAtlasCancellationSectionNormed_rb3c04b_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance catalogAtlasCancellationSectionSpace_rb3c04b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem finite_catalog_atlas_cancellation
    (Γ : A.centers → Finset (SmallModes.Base → ℝ))
    (hΓ : ∀ i φ, φ ∈ Γ i → ContDiff ℝ ∞ φ)
    {ε b D : ℝ} (hε : 0 < ε) (hb : 0 < b) (hD : 1 ≤ D) (hDB : (ε*b)⁻¹ ≤ D)
    (B : ℕ → ℝ → ℝ) (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
    ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
      ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)],
      ∀ x : ℝ, 1 ≤ x →
      ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F)
        (φ : (i : A.centers) → ι i → SmallModes.Base → ℝ),
      (∀ i j, φ i j ∈ Γ i) →
      ∀ K : (i : A.centers) → ι i → TopologicalSpace.Compacts SmallModes.Base,
      (∀ i j, (K i j : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      (∀ i j y, y ∈ (K i j : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) y)) →
      (∀ i j y, y ∈ (K i j : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y‖) →
      (∀ i j y, y ∈ (K i j : Set SmallModes.Base) →
        ε*‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y‖ ≤
          ‖PhaseGeometry.secondQuadratic
            (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
            (-(phaseDerivative (φ i j) y).2,(phaseDerivative (φ i j) y).1)‖) →
      (∀ i j y, y ∈ (K i j : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i F) y))⁻¹‖ ≤ D) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ i m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (B m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (K i j),
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (E m*x^(d m)*(∑ i : A.centers, ∑ j, supportedWeightedSeminorm (K i j) s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j))) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ/s)^(q+1)*(E m*x^(d m))*(∑ i : A.centers, ∑ j,
            supportedWeightedSeminorm (K i j) s
              (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (target i j)))
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun i y => ∑ j,
              QuadraticMean.displacement τ (φ i j) (target i j) y))) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
