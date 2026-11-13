-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phaseAtlasAnsatz_defect
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_defect
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:42:21.762595+00:00
-- url     : https://prove2.me/theorems/da353cdd-5971-46f4-b2db-3e3220261a41
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_defect: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_defect` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/NonlinearAtlasMetric.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/NonlinearAtlasMetric.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology`, `open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector`):
--
--   ```lean
--   lemma phaseAtlasAnsatz_defect (i : A.centers) {F : M → Space}
--       (hF : ContMDiff planeModel spaceModel ∞ F)
--       (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
--       (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
--       {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
--       (hχs : tsupport χ ⊆ e.source)
--       {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
--       {K : Set JetPolynomial.Base} (hK : IsCompact K) (hKO : K ⊆ O)
--       (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
--       (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
--       (hone : ∀ x ∈ e.symm '' K, χ x = 1)
--       (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
--       {n : ℕ} (P : Fin 3 → Fin n → Expression)
--       (γ : ∀ x : M, CovariantTwoTensor x) (B : JetPolynomial.Base → PhaseMean.Tensor) :
--       inducedTensor (A.phaseAtlasAnsatz i F e χ U ℓ L z) -
--           (γ + A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (localizedTensorPullback e χ B y))) =
--         (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i
--           (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))) z F - γ) +
--         A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
--           (localizedTensorPullback e χ (A.phaseAtlasRemainder i F e U ℓ L z P B) y))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.CovarianceCorrector.Period`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.bundleRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.fiberFromThree` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.val` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialMetric` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.localizedTensorPullback`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveAtlasPolynomial`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.cutoffTensorPolynomial` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorPolynomialCoordinatePullback` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearMetricDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearMetricFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearMetricFiberSpace` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasRemainder` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_error_bound` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/NonlinearAtlasMetric.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_defect)

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
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearMetricDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearMetricFiberSpace
local instance nonlinearMetricDualSmul_r6a7775_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearMetricFiberNormed
local instance nonlinearMetricSectionNormed_r6a7775_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance nonlinearMetricSectionSpace_r6a7775_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma phaseAtlasAnsatz_defect (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K) (hKO : K ⊆ O)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (γ : ∀ x : M, CovariantTwoTensor x) (B : JetPolynomial.Base → PhaseMean.Tensor) :
    inducedTensor (A.phaseAtlasAnsatz i F e χ U ℓ L z) -
        (γ + A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (localizedTensorPullback e χ B y))) =
      (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i
        (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))) z F - γ) +
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (localizedTensorPullback e χ (A.phaseAtlasRemainder i F e U ℓ L z P B) y)) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
