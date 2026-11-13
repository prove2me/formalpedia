-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_independent_circular_realization
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.independent_circular_realization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:42.037808+00:00
-- url     : https://prove2.me/theorems/82aba73c-6b49-4e46-8377-6f7f784105f0
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.independent_circular_realization: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.independent_circular_realization` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentCircularRealization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentCircularRealization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open SmallModes PhaseGeometry`):
--
--   ```lean
--   theorem independent_circular_realization (g : SmoothMetric M) (c C : ℝ)
--       (B : SmoothingAtlas M) (r L K : B.centers → ℝ)
--       (hL : ∀ i, 0 < L i)
--       (hreg : ∀ i : B.centers, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target)
--       (hnon : ∀ i p, 0 ≤ B.weight i p)
--       (hpos : ∀ i p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) (r i))
--       (hphase : ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 (C+1) h.inner →
--         (∀ q v, c*g.inner q v v ≤ h.inner q v v) →
--         ∀ (i : B.centers) (q : M), q ∈ circularDiskClosure (i : M) (r i) →
--           ∀ ell : Base, ‖ell‖ ≤ K i → ∀ v : Base,
--             (L i/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h (i : M))
--               (centeredConvexPhase ell (L i) (coordinateChart (i : M) i))
--               (coordinateChart (i : M) q) v v)
--       (m : ℕ) (D : ℝ) (hD : 0 ≤ D) :
--       ∃ N : ℕ, 0 < N ∧ ∀ g₀ : SmoothMetric M,
--         (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) →
--         ∀ (u : ∀ p : M, CovariantTwoTensor p)
--           (f : Fin N → SmoothPrimitiveFamily (Fin m) u),
--         (∀ k a, A.TensorWeightedBound 1 1 D ((f k).term a)) →
--         (∀ k : Fin N, A.TensorWeightedBound 1 1 C (g₀.inner+((k.val : ℝ)/(N : ℝ)) • u)) →
--         ∀ d : CircularPrimitiveFamily B (Fin (N*m)),
--         (∀ a p, d.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) →
--         (∀ a, d.phase a = (f a.divNat).phase a.modNat) →
--         (∀ a, d.convexPart a = L (d.curves a).index) →
--         (∀ a, ‖d.linearPart a‖ ≤ K (d.curves a).index) →
--         ∀ h : SmoothMetric M, h.inner = g₀.inner+u →
--         ∀ (F : M → Space) (n : PreferredNormal F), IsSmoothIsometricImmersion M g₀ F →
--           MetricGoodPhaseData g₀ F →
--           FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n →
--         ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PreferredNormal` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.coordinateChart`, `OAI.ClosedSurfaceR4.coordinateMetric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryCrossingSet`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularCoordinateDisk`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularCoordinateRegion`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularDiskClosure`, `OAI.ClosedSurfaceR4.PhaseGeometry.centeredConvexPhase`, `OAI.ClosedSurfaceR4.PhaseGeometry.coordinateMetricHessian`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily.term` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.FiniteBoundaryGeometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily.cycleAmplitude` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.isometric_immersion_of_spherical_immersion` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentCircularRealization.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.independent_circular_realization)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem independent_circular_realization (g : SmoothMetric M) (c C : ℝ)
    (B : SmoothingAtlas M) (r L K : B.centers → ℝ)
    (hL : ∀ i, 0 < L i)
    (hreg : ∀ i : B.centers, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target)
    (hnon : ∀ i p, 0 ≤ B.weight i p)
    (hpos : ∀ i p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) (r i))
    (hphase : ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 (C+1) h.inner →
      (∀ q v, c*g.inner q v v ≤ h.inner q v v) →
      ∀ (i : B.centers) (q : M), q ∈ circularDiskClosure (i : M) (r i) →
        ∀ ell : Base, ‖ell‖ ≤ K i → ∀ v : Base,
          (L i/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h (i : M))
            (centeredConvexPhase ell (L i) (coordinateChart (i : M) i))
            (coordinateChart (i : M) q) v v)
    (m : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ N : ℕ, 0 < N ∧ ∀ g₀ : SmoothMetric M,
      (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) →
      ∀ (u : ∀ p : M, CovariantTwoTensor p)
        (f : Fin N → SmoothPrimitiveFamily (Fin m) u),
      (∀ k a, A.TensorWeightedBound 1 1 D ((f k).term a)) →
      (∀ k : Fin N, A.TensorWeightedBound 1 1 C (g₀.inner+((k.val : ℝ)/(N : ℝ)) • u)) →
      ∀ d : CircularPrimitiveFamily B (Fin (N*m)),
      (∀ a p, d.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) →
      (∀ a, d.phase a = (f a.divNat).phase a.modNat) →
      (∀ a, d.convexPart a = L (d.curves a).index) →
      (∀ a, ‖d.linearPart a‖ ≤ K (d.curves a).index) →
      ∀ h : SmoothMetric M, h.inner = g₀.inner+u →
      ∀ (F : M → Space) (n : PreferredNormal F), IsSmoothIsometricImmersion M g₀ F →
        MetricGoodPhaseData g₀ F →
        FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n →
      ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
