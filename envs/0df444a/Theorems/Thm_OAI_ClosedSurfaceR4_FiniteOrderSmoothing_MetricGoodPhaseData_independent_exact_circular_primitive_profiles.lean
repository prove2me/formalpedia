-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_exact_circular_primitive_profiles
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_profiles
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:35:53.972959+00:00
-- url     : https://prove2.me/theorems/c94fefac-9d15-4c3c-9f00-9e8f11291ab6
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_profiles (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_profiles` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentExactCircular.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentExactCircular.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology`, `open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation`, `open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame`):
--
--   ```lean
--   theorem independent_exact_circular_primitive_profiles [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
--       (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
--       (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
--       (i : A₀.centers)
--       (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
--       (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
--       {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
--       (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
--       (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
--       {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
--       {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
--       {Z : TopologicalSpace.Opens GeometricJet} (hOZ : (O : Set LowJet) ⊆ jetDomain Z)
--       {e₁ e₂ : GeometricJet → NormalFrame.Vec}
--       (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
--       {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
--       (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
--         velocityRadius (normal J) (a (decode J).1) •
--           VelocityFrame.direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
--       (S : TopologicalSpace.Opens JetPolynomial.Base)
--       (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
--       {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
--       (hFQ : MapsTo (lowJet (A₀.jetChartMap i F ∘ e.symm)) S Q)
--       (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
--       (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
--       (hone : ∀ x ∈ e.symm '' K, χ x = 1)
--       (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J)
--       (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
--       (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)
--
--       (h : SmoothMetric M)
--       (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
--         (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
--       {C : Set JetPolynomial.Base} (hC : IsCompact C)
--       (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target) :
--       ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
--       ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
--         IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
--         (∀ p ∈ C, ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧
--           ‖realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z (baseEquiv p)-
--             surfaceCircularProfile (A₀.phaseRealChartMap i e.symm F) a e₁ e₂ α (baseEquiv p,t)‖ < ε) ∧
--         ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
--           A₀.WeightedBound 1 3 ε (G-F) ∧
--           ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
--             A₀.WeightedBound 1 2 (z^8) (W-V) ∧
--             (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
--           ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.coordinateVector`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJet`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.TransverseSmallFunction.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.bundleRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.fiberFromThree`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.RealTwoJet`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.normal` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.HasSpatialAmplitude` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.GeometryPreservation.BoundaryProfile`, `OAI.ClosedSurfaceR4.VelocityFrame.velocityRadius` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.VelocityFrame.direction` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.GeometryPreservation.realBoundaryProfile`, `OAI.ClosedSurfaceR4.JetPolynomial.localizedTensorPullback` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseSurfaceSupport` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.decode`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.GeometricJet` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetDomain` (definitions bundle `OAIQ249SI009` of this split); `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.surfaceCircularProfile` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactCircularPrimitiveDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactCircularPrimitiveFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactCircularPrimitiveFiberSpace` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseRealChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_boundary` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentExactCircular.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_profiles)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactCircularPrimitiveDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactCircularPrimitiveFiberSpace
local instance independent_exactCircularPrimitiveDualSmul_r74d83a_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactCircularPrimitiveFiberNormed
local instance independent_exactCircularPrimitiveSectionNormed_r74d83a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independent_exactCircularPrimitiveSectionSpace_r74d83a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem independent_exact_circular_primitive_profiles [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {Z : TopologicalSpace.Opens GeometricJet} (hOZ : (O : Set LowJet) ⊆ jetDomain Z)
    {e₁ e₂ : GeometricJet → NormalFrame.Vec}
    (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        VelocityFrame.direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (A₀.jetChartMap i F ∘ e.symm)) S Q)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target) :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p ∈ C, ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧
        ‖realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z (baseEquiv p)-
          surfaceCircularProfile (A₀.phaseRealChartMap i e.symm F) a e₁ e₂ α (baseEquiv p,t)‖ < ε) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  sorry

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
