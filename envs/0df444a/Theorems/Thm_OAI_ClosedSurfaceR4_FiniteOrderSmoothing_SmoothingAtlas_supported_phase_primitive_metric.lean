-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_supported_phase_primitive_metric
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_phase_primitive_metric
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:41.040401+00:00
-- url     : https://prove2.me/theorems/73deda55-64bd-43cb-a8c9-b33a71ad15ff
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_phase_primitive_metric: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_phase_primitive_metric` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/NonlinearPrimitiveExpansion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/NonlinearPrimitiveExpansion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology`, `open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector`):
--
--   ```lean
--   theorem supported_phase_primitive_metric (i : A.centers)
--       (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
--       (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
--       {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
--       (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
--       {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
--       {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
--       (S : TopologicalSpace.Opens JetPolynomial.Base) (hTS : MapsTo e e.source S)
--       {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
--       (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
--       (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
--       ∃ P : Fin 3 → Fin n → Expression, (∀ k r, (P k r).SmoothCoeffs univ) ∧
--       ∃ loss : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ Dv D : ℝ, 0 ≤ Dv ∧ 0 ≤ D ∧
--         ∀ (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
--           (hGQ : MapsTo (lowJet (A.jetChartMap i G ∘ e.symm)) S Q),
--         ∀ K : Set JetPolynomial.Base, IsCompact K → K ⊆ S →
--         e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) →
--         (∀ x ∈ e.symm '' K, χ x = 1) →
--         (∀ p ∈ S, p ∉ K → ∀ t,
--           l.velocity (lowJet (A.jetChartMap i G ∘ e.symm) p,t) =
--             SurfaceVelocityFamily.normal (lowJet (A.jetChartMap i G ∘ e.symm) p)) →
--         ∃ U : ℕ → Family S Space,
--           (∀ j p, p ∉ K → (U j).val p = 0) ∧
--           (∀ j, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U j).val y.1 (y.2 : Period))) ∧
--           (∀ j, VectorExpression.Represents (A.jetChartMap i G ∘ e.symm) (l.coefficientExpressions n j) (U j)) ∧
--           U 0 = (l.geometry (A.jetChartMap i G ∘ e.symm) ((A.jetChartMap_smooth i hG).comp hi)
--             (fun _ hp => hQO (hGQ hp))).initial ∧
--           (∀ z, ContMDiff planeModel spaceModel ∞ (A.phaseAtlasAnsatz i G e χ U ℓ (n+1) z)) ∧
--         ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
--           WeightedEstimates.WeightedBound S s (m+(2*(n+1)+1)) B (lowJet (A.jetChartMap i G ∘ e.symm)) →
--           A.WeightedBound z m (Dv*z/s^loss) (A.phaseAtlasAnsatz i G e χ U ℓ (n+1) z-G) ∧
--           ∀ (γ : ∀ x : M, CovariantTwoTensor x),
--             ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--               (fun x => TotalSpace.mk' TensorFiber x (γ x)) →
--           ∀ C : ℝ, A.TensorWeightedBound z m C
--             (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i
--               (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))) z G-γ) →
--           A.TensorWeightedBound z m (C+D*z^(n+1)/s^loss)
--             (inducedTensor (A.phaseAtlasAnsatz i G e χ U ℓ (n+1) z)-
--               (γ+A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
--                 (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.CovarianceCorrector.Period`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.coordinateVector`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJet`, `OAI.ClosedSurfaceR4.JetVelocityCoordinates.Euclidean`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.bundleRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.fiberFromThree`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.normal` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.HasSpatialAmplitude` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.val` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialMetric` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap_smooth` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.localizedTensorPullback`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveAtlasPolynomial`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.cutoffTensorPolynomial` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorPolynomialCoordinatePullback` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseExpansionDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseExpansionDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseExpansionFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseExpansionFiberSpace` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.geometry` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz`, `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.Represents`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.initial` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.coefficientExpressions` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/NonlinearPrimitiveExpansion.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_phase_primitive_metric)

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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseExpansionDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseExpansionDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseExpansionFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseExpansionFiberSpace
local instance phaseExpansionSectionNormed_rb787eb_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseExpansionSectionSpace_rb787eb_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem supported_phase_primitive_metric (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
    (S : TopologicalSpace.Opens JetPolynomial.Base) (hTS : MapsTo e e.source S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ P : Fin 3 → Fin n → Expression, (∀ k r, (P k r).SmoothCoeffs univ) ∧
    ∃ loss : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ Dv D : ℝ, 0 ≤ Dv ∧ 0 ≤ D ∧
      ∀ (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
        (hGQ : MapsTo (lowJet (A.jetChartMap i G ∘ e.symm)) S Q),
      ∀ K : Set JetPolynomial.Base, IsCompact K → K ⊆ S →
      e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) →
      (∀ x ∈ e.symm '' K, χ x = 1) →
      (∀ p ∈ S, p ∉ K → ∀ t,
        l.velocity (lowJet (A.jetChartMap i G ∘ e.symm) p,t) =
          SurfaceVelocityFamily.normal (lowJet (A.jetChartMap i G ∘ e.symm) p)) →
      ∃ U : ℕ → Family S Space,
        (∀ j p, p ∉ K → (U j).val p = 0) ∧
        (∀ j, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U j).val y.1 (y.2 : Period))) ∧
        (∀ j, VectorExpression.Represents (A.jetChartMap i G ∘ e.symm) (l.coefficientExpressions n j) (U j)) ∧
        U 0 = (l.geometry (A.jetChartMap i G ∘ e.symm) ((A.jetChartMap_smooth i hG).comp hi)
          (fun _ hp => hQO (hGQ hp))).initial ∧
        (∀ z, ContMDiff planeModel spaceModel ∞ (A.phaseAtlasAnsatz i G e χ U ℓ (n+1) z)) ∧
      ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
        WeightedEstimates.WeightedBound S s (m+(2*(n+1)+1)) B (lowJet (A.jetChartMap i G ∘ e.symm)) →
        A.WeightedBound z m (Dv*z/s^loss) (A.phaseAtlasAnsatz i G e χ U ℓ (n+1) z-G) ∧
        ∀ (γ : ∀ x : M, CovariantTwoTensor x),
          ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
            (fun x => TotalSpace.mk' TensorFiber x (γ x)) →
        ∀ C : ℝ, A.TensorWeightedBound z m C
          (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i
            (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))) z G-γ) →
        A.TensorWeightedBound z m (C+D*z^(n+1)/s^loss)
          (inducedTensor (A.phaseAtlasAnsatz i G e χ U ℓ (n+1) z)-
            (γ+A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
              (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y)))) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
