-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_circular_primitive_boundary_step
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_circular_primitive_boundary_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:36:15.983722+00:00
-- url     : https://prove2.me/theorems/c4ad8d4b-ef05-4ac2-853a-ab23170a8f96
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_circular_primitive_boundary_step (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_circular_primitive_boundary_step` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentCircularBoundaryStep.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentCircularBoundaryStep.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology`, `open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation`, `open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame`):
--
--   ```lean
--   theorem independent_circular_primitive_boundary_step [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
--       (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
--       (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
--       (i : A₀.centers)
--       (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
--       (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
--       {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
--       (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
--       (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
--       {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
--       {n : SmallModes.Base → NormalFrame.Vec} {T U : Set SmallModes.Base}
--       (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
--       (hn : ContDiffOn ℝ ∞ n U)
--       (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ (A₀.phaseRealChartMap i e.symm F) p))
--       (hN : ∀ p ∈ U, SmallModes.coordDeriv SmallModes.dx (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧
--         SmallModes.coordDeriv SmallModes.dy (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
--       (hHess : ∀ p ∈ U, 0 < PhaseGeometry.coordinateMetricHessian
--         (RealModes.inducedCoordinateMetric (A₀.phaseRealChartMap i e.symm F)) Prod.fst p SmallModes.dy SmallModes.dy)
--       (ha0 : ∀ p, 0 ≤ a p)
--       (hboundary : ∀ p ∈ T, a p = 0 →
--         realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p ≠ 0 ∧
--         normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p) ≠ -n p)
--       {ι : Type*} [Finite ι] {Curves : ι → Set SmallModes.Base}
--       (hCurves : ∀ j, IsCompact (Curves j)) (hCurvesT : ∀ j, Curves j ⊆ T)
--       {P : Set SmallModes.Base} (hP : P.Finite)
--       (hlocal : ∀ p ∈ (⋃ j, Curves j) \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
--         ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧
--           (∀ x ∈ (⋃ j, Curves j) ∩ N, f x = 0) ∧ fderiv ℝ f p (0,1) ≠ 0)
--       {E : Set SmallModes.Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
--       (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
--       {b c : ι → SmallModes.Base → ℝ}
--       (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hc : ∀ j, ContDiff ℝ ∞ (c j))
--       (hbc : ∀ j, ∀ x ∈ Curves j, b j x ≠ 0 ∨ c j x ≠ 0)
--       (S : TopologicalSpace.Opens JetPolynomial.Base)
--       (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
--       (hST : baseEquiv '' closure (S : Set JetPolynomial.Base) ⊆ T)
--       (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
--       (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
--       (hone : ∀ x ∈ e.symm '' K, χ x = 1)
--       (haoff : ∀ p ∉ K, a (baseEquiv p) = 0)
--       (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
--       (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)
--
--       (h : SmoothMetric M)
--       (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
--         (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
--       {C : Set JetPolynomial.Base} (hC : IsCompact C)
--       (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target)
--       (hCurveC : ∀ j x, x ∈ Curves j → baseEquiv.symm x ∈ C)
--       (hactiveC : ∀ p ∈ C, A₀.chartWeight i (e.symm p) ≠ 0)
--       (hEC : ∀ x ∈ E, baseEquiv.symm x ∈ C)
--       (hold : ∀ j, ∀ x ∈ Curves j, a x = 0 →
--         let H := A₀.phaseRealChartMap i e.symm F
--         let κ := coordinateGaussianCurvature (realMetric H SmallModes.dx SmallModes.dx)
--           (realMetric H SmallModes.dx SmallModes.dy) (realMetric H SmallModes.dy SmallModes.dy) x
--         0 < orderedCrossing H SmallModes.dy (b j x,c j x) x κ)
--
--       {σ : Type*} [Fintype σ] [DecidableEq σ]
--       (left right : σ → ι) (x : σ → SmallModes.Base) (hxinj : Function.Injective x)
--       (hxE : ∀ j, x j ∈ E)
--       {V : Set SmallModes.Base} (hV : IsOpen V) (hxV : ∀ j, x j ∈ V)
--       (honly : ∀ j k, x j ∈ Curves k → k = left j ∨ k = right j)
--       (hfirst : ∀ j, b (left j) (x j) ≠ 0 ∧ b (right j) (x j) ≠ 0)
--       (hslopes : ∀ j, |c (left j) (x j)/b (left j) (x j)| ≤ slopeBound ∧
--         |c (right j) (x j)/b (right j) (x j)| ≤ slopeBound)    (B : SmoothingAtlas M) (curves : ι → PhaseBoundaryCurve B)
--       (n₀ : PreferredNormal F)
--       (hglobal : ∀ j p, p ∈ (curves j).carrier → (curves j).second F p ≠ 0 ∧
--         spaceCoordinates (n₀.vector p) ≠ -normalize ((curves j).second F p))
--       {D : Set M} (hD : IsOpen D) (hDr : interior (closure D) = D)
--       (hDs : closure D ⊆ (chart (i : M)).source)
--       (hDe : MapsTo (chart (i : M)) (closure D) e.source)
--       (hDw : ∀ p ∈ closure D, A₀.weight i p ≠ 0)
--       (E₀ : Set M) (hE₀ : E₀.Finite) (hE₀f : Disjoint E₀ (frontier D))
--       (hsupport : A₀.phaseSurfaceSupport i e K = closure D)
--       (hDC : ∀ p ∈ closure D, e (chart (i : M) p) ∈ C)
--       (hcurveChart : ∀ j p, p ∈ (curves j).carrier → p ∈ closure D →
--         baseEquiv (e (chart (i : M) p)) ∈ Curves j)
--       (hvector : ∀ j p, p ∈ (curves j).carrier → p ∈ closure D →
--         (b j (baseEquiv (e (chart (i : M) p))),c j (baseEquiv (e (chart (i : M) p)))) =
--           fderiv ℝ (surfacePhaseTransition ((curves j).index : M) (curves j).phase (i : M) e)
--             ((curves j).coordinate p) SmallModes.dy)
--       (hworldBoundary : ∀ p ∈ frontier D,
--         realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy
--           (baseEquiv (e (chart (i : M) p))) ≠ 0 ∧
--         spaceCoordinates (n₀.vector p) ≠ -normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F)
--           SmallModes.dy SmallModes.dy (baseEquiv (e (chart (i : M) p)))))
--       (haFrontier : ∀ p ∈ frontier D, a (baseEquiv (e (chart (i : M) p))) = 0)
--       (hpositive : ∀ j p, p ∈ (curves j).carrier → p ∈ frontier D →
--         0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n₀.vector p))
--       (hVfrontier : ∀ p ∈ frontier D, baseEquiv (e (chart (i : M) p)) ∉ V)
--       (hσD : ∀ j, (surfacePhaseChart (i : M) e).symm (x j) ∈ E₀ ∩ D)    (hinsideCover : ∀ p ∈ E₀, p ∈ D → ∃ s, (surfacePhaseChart (i : M) e).symm (x s) = p)
--       (hglobalCross : ∀ j k, j ≠ k → ∀ p ∈ E₀,
--         p ∈ (curves j).carrier → p ∈ (curves k).carrier →
--         (0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n₀.vector p) ∧
--          0 < (curves k).second F p ⬝ᵥ spaceCoordinates (n₀.vector p)) ∧
--         0 < (curves j).crossing (curves k) F p ∧ 0 < (curves k).crossing (curves j) F p) :
--       ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
--         ∃ N : PreferredNormal W,
--           (∀ j p, p ∈ (curves j).carrier → (curves j).second W p ≠ 0 ∧
--             spaceCoordinates (N.vector p) ≠ -normalize ((curves j).second W p)) ∧
--           ∀ j k, j ≠ k → ∀ p ∈ E₀, p ∈ (curves j).carrier → p ∈ (curves k).carrier →
--             (0 < (curves j).second W p ⬝ᵥ spaceCoordinates (N.vector p) ∧
--              0 < (curves k).second W p ⬝ᵥ spaceCoordinates (N.vector p)) ∧
--             0 < (curves j).crossing (curves k) W p ∧ 0 < (curves k).crossing (curves j) W p
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.coordinateVector`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.bundleRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PreferredNormal` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.fiberFromThree`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor`, `OAI.ClosedSurfaceR4.PhaseGeometry.coordinateMetricHessian`, `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realMetric`, `OAI.ClosedSurfaceR4.RealModes.realSecondForm`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv`, `OAI.ClosedSurfaceR4.VelocityFrame.normalize` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.coordinate` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.localizedTensorPullback`, `OAI.ClosedSurfaceR4.RealModes.inducedCoordinateMetric` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseSurfaceSupport` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_boundaryCircularPrimitiveDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_boundaryCircularPrimitiveFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_boundaryCircularPrimitiveFiberSpace` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.surfacePhaseChart`, `OAI.ClosedSurfaceR4.surfacePhaseTransition`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData`, `OAI.ClosedSurfaceR4.RealModes.coordinateGaussianCurvature`, `OAI.ClosedSurfaceR4.VelocityFrame.orderedCrossing`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.crossing`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.second` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseRealChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_CircularPrimitiveFamily_realize_total` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.boundary_step` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentCircularBoundaryStep.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_circular_primitive_boundary_step)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
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
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_boundaryCircularPrimitiveDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_boundaryCircularPrimitiveFiberSpace
local instance independent_boundaryCircularPrimitiveDualSmul_rc88da1_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_boundaryCircularPrimitiveFiberNormed
local instance independent_boundaryCircularPrimitiveSectionNormed_rc88da1_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independent_boundaryCircularPrimitiveSectionSpace_rc88da1_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem independent_circular_primitive_boundary_step [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {n : SmallModes.Base → NormalFrame.Vec} {T U : Set SmallModes.Base}
    (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ (A₀.phaseRealChartMap i e.symm F) p))
    (hN : ∀ p ∈ U, SmallModes.coordDeriv SmallModes.dx (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧
      SmallModes.coordDeriv SmallModes.dy (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A₀.phaseRealChartMap i e.symm F)) Prod.fst p SmallModes.dy SmallModes.dy)
    (ha0 : ∀ p, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 →
      realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p ≠ 0 ∧
      normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p) ≠ -n p)
    {ι : Type*} [Finite ι] {Curves : ι → Set SmallModes.Base}
    (hCurves : ∀ j, IsCompact (Curves j)) (hCurvesT : ∀ j, Curves j ⊆ T)
    {P : Set SmallModes.Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ j, Curves j) \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧
        (∀ x ∈ (⋃ j, Curves j) ∩ N, f x = 0) ∧ fderiv ℝ f p (0,1) ≠ 0)
    {E : Set SmallModes.Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
    (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
    {b c : ι → SmallModes.Base → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hc : ∀ j, ContDiff ℝ ∞ (c j))
    (hbc : ∀ j, ∀ x ∈ Curves j, b j x ≠ 0 ∨ c j x ≠ 0)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    (hST : baseEquiv '' closure (S : Set JetPolynomial.Base) ⊆ T)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (haoff : ∀ p ∉ K, a (baseEquiv p) = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target)
    (hCurveC : ∀ j x, x ∈ Curves j → baseEquiv.symm x ∈ C)
    (hactiveC : ∀ p ∈ C, A₀.chartWeight i (e.symm p) ≠ 0)
    (hEC : ∀ x ∈ E, baseEquiv.symm x ∈ C)
    (hold : ∀ j, ∀ x ∈ Curves j, a x = 0 →
      let H := A₀.phaseRealChartMap i e.symm F
      let κ := coordinateGaussianCurvature (realMetric H SmallModes.dx SmallModes.dx)
        (realMetric H SmallModes.dx SmallModes.dy) (realMetric H SmallModes.dy SmallModes.dy) x
      0 < orderedCrossing H SmallModes.dy (b j x,c j x) x κ)

    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (left right : σ → ι) (x : σ → SmallModes.Base) (hxinj : Function.Injective x)
    (hxE : ∀ j, x j ∈ E)
    {V : Set SmallModes.Base} (hV : IsOpen V) (hxV : ∀ j, x j ∈ V)
    (honly : ∀ j k, x j ∈ Curves k → k = left j ∨ k = right j)
    (hfirst : ∀ j, b (left j) (x j) ≠ 0 ∧ b (right j) (x j) ≠ 0)
    (hslopes : ∀ j, |c (left j) (x j)/b (left j) (x j)| ≤ slopeBound ∧
      |c (right j) (x j)/b (right j) (x j)| ≤ slopeBound)    (B : SmoothingAtlas M) (curves : ι → PhaseBoundaryCurve B)
    (n₀ : PreferredNormal F)
    (hglobal : ∀ j p, p ∈ (curves j).carrier → (curves j).second F p ≠ 0 ∧
      spaceCoordinates (n₀.vector p) ≠ -normalize ((curves j).second F p))
    {D : Set M} (hD : IsOpen D) (hDr : interior (closure D) = D)
    (hDs : closure D ⊆ (chart (i : M)).source)
    (hDe : MapsTo (chart (i : M)) (closure D) e.source)
    (hDw : ∀ p ∈ closure D, A₀.weight i p ≠ 0)
    (E₀ : Set M) (hE₀ : E₀.Finite) (hE₀f : Disjoint E₀ (frontier D))
    (hsupport : A₀.phaseSurfaceSupport i e K = closure D)
    (hDC : ∀ p ∈ closure D, e (chart (i : M) p) ∈ C)
    (hcurveChart : ∀ j p, p ∈ (curves j).carrier → p ∈ closure D →
      baseEquiv (e (chart (i : M) p)) ∈ Curves j)
    (hvector : ∀ j p, p ∈ (curves j).carrier → p ∈ closure D →
      (b j (baseEquiv (e (chart (i : M) p))),c j (baseEquiv (e (chart (i : M) p)))) =
        fderiv ℝ (surfacePhaseTransition ((curves j).index : M) (curves j).phase (i : M) e)
          ((curves j).coordinate p) SmallModes.dy)
    (hworldBoundary : ∀ p ∈ frontier D,
      realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy
        (baseEquiv (e (chart (i : M) p))) ≠ 0 ∧
      spaceCoordinates (n₀.vector p) ≠ -normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F)
        SmallModes.dy SmallModes.dy (baseEquiv (e (chart (i : M) p)))))
    (haFrontier : ∀ p ∈ frontier D, a (baseEquiv (e (chart (i : M) p))) = 0)
    (hpositive : ∀ j p, p ∈ (curves j).carrier → p ∈ frontier D →
      0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n₀.vector p))
    (hVfrontier : ∀ p ∈ frontier D, baseEquiv (e (chart (i : M) p)) ∉ V)
    (hσD : ∀ j, (surfacePhaseChart (i : M) e).symm (x j) ∈ E₀ ∩ D)    (hinsideCover : ∀ p ∈ E₀, p ∈ D → ∃ s, (surfacePhaseChart (i : M) e).symm (x s) = p)
    (hglobalCross : ∀ j k, j ≠ k → ∀ p ∈ E₀,
      p ∈ (curves j).carrier → p ∈ (curves k).carrier →
      (0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n₀.vector p) ∧
       0 < (curves k).second F p ⬝ᵥ spaceCoordinates (n₀.vector p)) ∧
      0 < (curves j).crossing (curves k) F p ∧ 0 < (curves k).crossing (curves j) F p) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ N : PreferredNormal W,
        (∀ j p, p ∈ (curves j).carrier → (curves j).second W p ≠ 0 ∧
          spaceCoordinates (N.vector p) ≠ -normalize ((curves j).second W p)) ∧
        ∀ j k, j ≠ k → ∀ p ∈ E₀, p ∈ (curves j).carrier → p ∈ (curves k).carrier →
          (0 < (curves j).second W p ⬝ᵥ spaceCoordinates (N.vector p) ∧
           0 < (curves k).second W p ⬝ᵥ spaceCoordinates (N.vector p)) ∧
          0 < (curves j).crossing (curves k) W p ∧ 0 < (curves k).crossing (curves j) W p := by
  sorry

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
