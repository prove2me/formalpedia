-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_grid_mean_data
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_grid_mean_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:43:49.378574+00:00
-- url     : https://prove2.me/theorems/a9967b64-82e0-4327-81b9-53d9c17efd95
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_grid_mean_data: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_grid_mean_data` of [lean/OAI/Geometry/SurfaceImmersion/Correction/GridMeanData.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/GridMeanData.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGrid PhaseGeometry RealModes`):
--
--   ```lean
--   theorem polynomial_grid_mean_data (g : SmoothMetric M) {a₀ C₀ H : ℝ}
--       (ha₀ : 0 < a₀) (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) :
--       ∃ (p p' : ℕ → ℕ) (C C' L : ℕ → ℝ),
--         (∀ m, 1 ≤ C m) ∧ (∀ m, 1 ≤ C' m) ∧ (∀ m, 1 ≤ L m) ∧
--       ∃ r ρ R : ℝ, 0 < r ∧ 0 < ρ ∧ 0 < R ∧
--       ∀ (z : ℝ) (hz : 0 < z), z ≤ 1 → ∀ a : A.centers → Finset Index,
--         (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion (a i) (z^6)) →
--       ∀ (Q : ∀ i, (a i) → PhaseBasis) (w : ∀ i, (a i) → Fin 3 → ℝ),
--         (∀ i k j, 1 ≤ w i k j) → (∀ i k j, ‖(Q i k).Q j‖ ≤ C₀) →
--         (∀ i k j x, (Q i k).Q j (A.tensorPlaneRead i g.inner x) ≤ H) →
--         (∀ i k j x, x ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
--           a₀ ≤ (Q i k).Q j (A.tensorPlaneRead i g.inner x)) →
--       ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
--         (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 → ∀ D : ℝ, 0 < D →
--       ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) → (∀ m, 2*D ≤ B m ∧ C₀ ≤ B m) →
--         (∀ i k j m, ‖w i k j • (Q i k).ξ j‖ ≤ B m ∧
--           ∀ hξ : w i k j • (Q i k).ξ j ≠ 0,
--             ‖(phaseEquiv (w i k j • (Q i k).ξ j) hξ).symm.toContinuousLinearMap‖ ≤ B m) →
--         (∀ i m l, l ≤ m+3 → WeightedEstimates.WeightedBound univ 1 l
--           (B m/(s : ℝ)^(l-2)) (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
--         (∀ i k j x, x ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
--           Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ∧
--           Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
--             (w i k j • (Q i k).ξ j) ∧
--           ‖(NormalFrame.gramDet
--             (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
--             (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x))⁻¹‖ ≤ D ∧
--           ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
--             (-(w i k j • (Q i k).ξ j).2,(w i k j • (Q i k).ξ j).1)‖⁻¹ ≤ D) →
--         ∃ c : ∀ i (j : (a i) × Fin 3), PolynomialSolveData emptyMetricPolynomial 0
--           (A.jetChartMap i F) (A.jetChartMap_smooth i hF)
--           (phaseLinear (w i j.1 j.2 • (Q i j.1).ξ j.2) ∘ planeCoordinateIsometry)
--           (A.cellChartCompact i (a i) (z^6) j.1.val) τ s,
--         ∃ d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i g.inner),
--           (∀ i j m, (c i j).C m = C m*(B m)^(p m) ∧
--             (c i j).J m = 1+2*B m ∧ (c i j).D m = 0) ∧
--           (∀ i j x, x ∈ (c i j).e.source → (d i j).cutoff ((c i j).e x) =
--             supportedCellCutoff (A.supportedPlaneWeight i) (pow_pos hz 6)
--               (hcover i) j.1.val x / w i j.1 j.2) ∧
--           (∀ i j, (d i j).form = fun _ => (Q i j.1).Q j.2) ∧
--           (∀ i j, tsupport (fun x => A.planeWeight i x * normalizedCutoff (a i) (z^6) j.1.val x) ⊆
--             (c i j).e.source) ∧
--           ∀ i j m, let b := linearMeanGeometryBudget p' C' B (fun l =>
--             1+phaseCutoffBudget l (L l/z^(6*l)) (B l) 1) m;
--             (d i j).budgets.inv m ≤ b ∧ (d i j).budgets.chi m ≤ b ∧
--             (d i j).budgets.forms m ≤ b ∧ (d i j).budgets.pull m ≤ b ∧
--             (d i j).budgets.psi m ≤ b ∧ (d i j).budgets.normal m ≤ b ∧ (d i j).budgets.mode m ≤ b
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.PhaseGrid.Index`, `OAI.ClosedSurfaceR4.PhaseGrid.coverRegion`, `OAI.ClosedSurfaceR4.PhaseGrid.gridCutoffCompact`, `OAI.ClosedSurfaceR4.PhaseGrid.normalizedCutoff`, `OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cellChartCompact` (definitions bundle `OAIQ249SI000` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.phaseCutoffBudget` and `OAI.ClosedSurfaceR4.PhaseMean.linearMeanGeometryBudget` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.phaseLinear`, `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.PhaseGeometry.Good`, `OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv`, `OAI.ClosedSurfaceR4.PhaseGeometry.secondQuadratic`, `OAI.ClosedSurfaceR4.PhaseGrid.Base`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.planeWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap_smooth` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.emptyMetricPolynomial`, `OAI.ClosedSurfaceR4.PhaseMean.Budgets`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.chartCompact` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.realMap` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorReadBallConstant` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/GridMeanData.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_grid_mean_data)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
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
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGrid PhaseGeometry RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance gridMeanDataFiberNormed_r48beff_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance gridMeanDataFiberSpace_r48beff_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance gridMeanDataDualAdd_r48beff_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridMeanDataDualSmul_r48beff_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance gridMeanDataSectionNormed_r48beff_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridMeanDataSectionSpace_r48beff_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_grid_mean_data (g : SmoothMetric M) {a₀ C₀ H : ℝ}
    (ha₀ : 0 < a₀) (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) :
    ∃ (p p' : ℕ → ℕ) (C C' L : ℕ → ℝ),
      (∀ m, 1 ≤ C m) ∧ (∀ m, 1 ≤ C' m) ∧ (∀ m, 1 ≤ L m) ∧
    ∃ r ρ R : ℝ, 0 < r ∧ 0 < ρ ∧ 0 < R ∧
    ∀ (z : ℝ) (hz : 0 < z), z ≤ 1 → ∀ a : A.centers → Finset Index,
      (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion (a i) (z^6)) →
    ∀ (Q : ∀ i, (a i) → PhaseBasis) (w : ∀ i, (a i) → Fin 3 → ℝ),
      (∀ i k j, 1 ≤ w i k j) → (∀ i k j, ‖(Q i k).Q j‖ ≤ C₀) →
      (∀ i k j x, (Q i k).Q j (A.tensorPlaneRead i g.inner x) ≤ H) →
      (∀ i k j x, x ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
        a₀ ≤ (Q i k).Q j (A.tensorPlaneRead i g.inner x)) →
    ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 → ∀ D : ℝ, 0 < D →
    ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) → (∀ m, 2*D ≤ B m ∧ C₀ ≤ B m) →
      (∀ i k j m, ‖w i k j • (Q i k).ξ j‖ ≤ B m ∧
        ∀ hξ : w i k j • (Q i k).ξ j ≠ 0,
          ‖(phaseEquiv (w i k j • (Q i k).ξ j) hξ).symm.toContinuousLinearMap‖ ≤ B m) →
      (∀ i m l, l ≤ m+3 → WeightedEstimates.WeightedBound univ 1 l
        (B m/(s : ℝ)^(l-2)) (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i k j x, x ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ∧
        Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
          (w i k j • (Q i k).ξ j) ∧
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x))⁻¹‖ ≤ D ∧
        ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
          (-(w i k j • (Q i k).ξ j).2,(w i k j • (Q i k).ξ j).1)‖⁻¹ ≤ D) →
      ∃ c : ∀ i (j : (a i) × Fin 3), PolynomialSolveData emptyMetricPolynomial 0
        (A.jetChartMap i F) (A.jetChartMap_smooth i hF)
        (phaseLinear (w i j.1 j.2 • (Q i j.1).ξ j.2) ∘ planeCoordinateIsometry)
        (A.cellChartCompact i (a i) (z^6) j.1.val) τ s,
      ∃ d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i g.inner),
        (∀ i j m, (c i j).C m = C m*(B m)^(p m) ∧
          (c i j).J m = 1+2*B m ∧ (c i j).D m = 0) ∧
        (∀ i j x, x ∈ (c i j).e.source → (d i j).cutoff ((c i j).e x) =
          supportedCellCutoff (A.supportedPlaneWeight i) (pow_pos hz 6)
            (hcover i) j.1.val x / w i j.1 j.2) ∧
        (∀ i j, (d i j).form = fun _ => (Q i j.1).Q j.2) ∧
        (∀ i j, tsupport (fun x => A.planeWeight i x * normalizedCutoff (a i) (z^6) j.1.val x) ⊆
          (c i j).e.source) ∧
        ∀ i j m, let b := linearMeanGeometryBudget p' C' B (fun l =>
          1+phaseCutoffBudget l (L l/z^(6*l)) (B l) 1) m;
          (d i j).budgets.inv m ≤ b ∧ (d i j).budgets.chi m ≤ b ∧
          (d i j).budgets.forms m ≤ b ∧ (d i j).budgets.pull m ≤ b ∧
          (d i j).budgets.psi m ≤ b ∧ (d i j).budgets.normal m ≤ b ∧ (d i j).budgets.mode m ≤ b := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
