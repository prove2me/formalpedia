-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_supported_local_metric_defect
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_local_metric_defect
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:54.760223+00:00
-- url     : https://prove2.me/theorems/72925cc3-8af1-4ecd-b0dd-f46ef4233277
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_local_metric_defect: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_local_metric_defect` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/SupportedLocalMetricDefect.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/SupportedLocalMetricDefect.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology`, `open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector`):
--
--   ```lean
--   lemma supported_local_metric_defect (i : A.centers) {F : M → Space}
--       (hF : ContMDiff planeModel spaceModel ∞ F) (f : JetPolynomial.Base → Space)
--       (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
--       {n : ℕ} (P : Fin 3 → Fin n → Expression) (z : ℝ)
--       (γ : ∀ x : M, CovariantTwoTensor x) (H : SmallModes.Base → PhaseMean.Tensor) :
--       inducedTensor (F + restore (i : M) (A.outer i) f) -
--           (γ + A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (H (planeCoordinateIsometry y)))) =
--         (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i P) z F - γ) +
--           A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
--             (RealModes.realMetricTensor
--                 (spaceCoordinates ∘ (A.vectorChartRead i F + f) ∘ planeCoordinateIsometry.symm)
--                   (planeCoordinateIsometry y) -
--               coordinateMetricMap P z (A.jetChartMap i F) (planeCoordinateIsometry y) -
--               H (planeCoordinateIsometry y)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.bundleRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.fiberFromThree`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realMetricTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorChartRead` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialMetric` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedLocalDefectDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedLocalDefectFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedLocalDefectFiberSpace` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveAtlasPolynomial` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinateMetricMap` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_defect` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/SupportedLocalMetricDefect.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_local_metric_defect)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedLocalDefectDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedLocalDefectFiberSpace
local instance supportedLocalDefectDualSmul_r3dee7c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedLocalDefectFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedLocalDefectSectionNormed
local instance supportedLocalDefectSectionSpace_r3dee7c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma supported_local_metric_defect (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (f : JetPolynomial.Base → Space)
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    {n : ℕ} (P : Fin 3 → Fin n → Expression) (z : ℝ)
    (γ : ∀ x : M, CovariantTwoTensor x) (H : SmallModes.Base → PhaseMean.Tensor) :
    inducedTensor (F + restore (i : M) (A.outer i) f) -
        (γ + A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (H (planeCoordinateIsometry y)))) =
      (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i P) z F - γ) +
        A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
          (RealModes.realMetricTensor
              (spaceCoordinates ∘ (A.vectorChartRead i F + f) ∘ planeCoordinateIsometry.symm)
                (planeCoordinateIsometry y) -
            coordinateMetricMap P z (A.jetChartMap i F) (planeCoordinateIsometry y) -
            H (planeCoordinateIsometry y))) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
