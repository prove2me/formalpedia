-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_geometric_normal_extension
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.geometric_normal_extension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:35:07.528942+00:00
-- url     : https://prove2.me/theorems/8d21e8fa-4afc-427e-8bab-2da04689dcf8
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.geometric_normal_extension: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.geometric_normal_extension` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/GeometricNormalExtension.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/GeometricNormalExtension.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open JetPolynomial SurfaceJetCoordinates RealModes SmallModes NormalFrame VelocityFrame GeometryPreservation`):
--
--   ```lean
--   theorem geometric_normal_extension
--       {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
--       (n : PreferredNormal F)
--       (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
--       (curves : κ → PhaseBoundaryCurve B)
--       (hold : ∀ k p, p ∈ (curves k).carrier → (curves k).second F p ≠ 0 ∧
--         spaceCoordinates (n.vector p) ≠ -normalize ((curves k).second F p))
--       (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
--       (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
--       {D : Set M} (hD : IsOpen D) (hDr : interior (closure D) = D)
--       (hDs : closure D ⊆ (chart (i : M)).source)
--       (hDe : MapsTo (chart (i : M)) (closure D) e.source)
--       (hDw : ∀ p ∈ closure D, A.weight i p ≠ 0)
--       (E : Set M) (hE : E.Finite) (hEf : Disjoint E (frontier D))
--       (v : κ → SmallModes.Base → SmallModes.Base) (hv : ∀ k, Continuous (v k))
--       (hvector : ∀ k p, p ∈ (curves k).carrier → p ∈ closure D →
--         v k (baseEquiv (e (chart (i : M) p))) =
--           fderiv ℝ (surfacePhaseTransition ((curves k).index : M) (curves k).phase (i : M) e)
--             ((curves k).coordinate p) dy)
--       (hboundary : ∀ p ∈ frontier D,
--         realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
--           (baseEquiv (e (chart (i : M) p))) ≠ 0 ∧
--         spaceCoordinates (n.vector p) ≠ -normalize (realSecondForm (A.phaseRealChartMap i e.symm F)
--           dy dy (baseEquiv (e (chart (i : M) p)))))
--       (hpositive : ∀ k p, p ∈ (curves k).carrier → p ∈ frontier D →
--         0 < (curves k).second F p ⬝ᵥ spaceCoordinates (n.vector p))
--       (hcross : ∀ k p, p ∈ (curves k).carrier → p ∈ frontier D →
--         let q := baseEquiv (e (chart (i : M) p))
--         let H := A.phaseRealChartMap i e.symm F
--         0 < orderedCrossing H dy (v k q) q
--           (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy) q)) :
--       ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
--         ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
--         ∀ h : SmoothMetric M, IsSmoothIsometricImmersion M h W →
--         ∀ b d : ℝ, 0 ≤ b → 0 ≤ d → b+d < ρ →
--         A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 d (W-V) →
--         (∀ p ∉ closure D, V =ᶠ[𝓝 p] G) →
--         ∀ z : ℝ, ∀ U₀ : Set SmallModes.Base, IsOpen U₀ → ∀ ν : SmallModes.Base → Vec,
--         ContDiffOn ℝ ∞ ν U₀ →
--         (∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1) →
--         (∀ x ∈ U₀, ∀ w : SmallModes.Base,
--           SmallModes.coordDeriv w (A.phaseRealChartMap i e.symm W) x ⬝ᵥ ν x = 0) →
--         MapsTo (fun p => baseEquiv (e (chart (i : M) p))) (closure D) U₀ →
--         (∀ p ∈ frontier D, ν (baseEquiv (e (chart (i : M) p))) =
--           profilePreferred (realBoundaryProfile (A.phaseRealChartMap i e.symm W) z
--             (baseEquiv (e (chart (i : M) p))))) →
--         (∀ k p, p ∈ (curves k).carrier → p ∈ D →
--           let q := baseEquiv (e (chart (i : M) p))
--           realSecondForm (A.phaseRealChartMap i e.symm W) (v k q) (v k q) q ≠ 0 ∧
--           ν q ≠ -normalize (realSecondForm (A.phaseRealChartMap i e.symm W) (v k q) (v k q) q)) →
--         ∃ N : PreferredNormal W,
--           (∀ k p, p ∈ (curves k).carrier → (curves k).second W p ≠ 0 ∧
--             spaceCoordinates (N.vector p) ≠ -normalize ((curves k).second W p)) ∧
--           ∀ p ∈ E, (p ∈ D → N.vector p = A.phaseNormalLift i e ν p) ∧
--             (p ∉ D → N.vector p = A.unitProjectedNormalField W n.vector p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base` and `OAI.ClosedSurfaceR4.NormalFrame.Vec` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PreferredNormal` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve`, `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realMetric`, `OAI.ClosedSurfaceR4.RealModes.realSecondForm`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv`, `OAI.ClosedSurfaceR4.VelocityFrame.normalize` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.coordinate` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.GeometryPreservation.profilePreferred`, `OAI.ClosedSurfaceR4.GeometryPreservation.realBoundaryProfile` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.unitProjectedNormalField` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseNormalLift` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.surfacePhaseTransition`, `OAI.ClosedSurfaceR4.RealModes.coordinateGaussianCurvature`, `OAI.ClosedSurfaceR4.VelocityFrame.orderedCrossing`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.second` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseRealChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_global_circular_primitive_normal` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/GeometricNormalExtension.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.geometric_normal_extension)

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
import Definitions.Def_OAIQ249SI011

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
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes NormalFrame VelocityFrame GeometryPreservation
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [Fintype κ]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem geometric_normal_extension
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (curves : κ → PhaseBoundaryCurve B)
    (hold : ∀ k p, p ∈ (curves k).carrier → (curves k).second F p ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize ((curves k).second F p))
    (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hD : IsOpen D) (hDr : interior (closure D) = D)
    (hDs : closure D ⊆ (chart (i : M)).source)
    (hDe : MapsTo (chart (i : M)) (closure D) e.source)
    (hDw : ∀ p ∈ closure D, A.weight i p ≠ 0)
    (E : Set M) (hE : E.Finite) (hEf : Disjoint E (frontier D))
    (v : κ → SmallModes.Base → SmallModes.Base) (hv : ∀ k, Continuous (v k))
    (hvector : ∀ k p, p ∈ (curves k).carrier → p ∈ closure D →
      v k (baseEquiv (e (chart (i : M) p))) =
        fderiv ℝ (surfacePhaseTransition ((curves k).index : M) (curves k).phase (i : M) e)
          ((curves k).coordinate p) dy)
    (hboundary : ∀ p ∈ frontier D,
      realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
        (baseEquiv (e (chart (i : M) p))) ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize (realSecondForm (A.phaseRealChartMap i e.symm F)
        dy dy (baseEquiv (e (chart (i : M) p)))))
    (hpositive : ∀ k p, p ∈ (curves k).carrier → p ∈ frontier D →
      0 < (curves k).second F p ⬝ᵥ spaceCoordinates (n.vector p))
    (hcross : ∀ k p, p ∈ (curves k).carrier → p ∈ frontier D →
      let q := baseEquiv (e (chart (i : M) p))
      let H := A.phaseRealChartMap i e.symm F
      0 < orderedCrossing H dy (v k q) q
        (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy) q)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ∀ h : SmoothMetric M, IsSmoothIsometricImmersion M h W →
      ∀ b d : ℝ, 0 ≤ b → 0 ≤ d → b+d < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 d (W-V) →
      (∀ p ∉ closure D, V =ᶠ[𝓝 p] G) →
      ∀ z : ℝ, ∀ U₀ : Set SmallModes.Base, IsOpen U₀ → ∀ ν : SmallModes.Base → Vec,
      ContDiffOn ℝ ∞ ν U₀ →
      (∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1) →
      (∀ x ∈ U₀, ∀ w : SmallModes.Base,
        SmallModes.coordDeriv w (A.phaseRealChartMap i e.symm W) x ⬝ᵥ ν x = 0) →
      MapsTo (fun p => baseEquiv (e (chart (i : M) p))) (closure D) U₀ →
      (∀ p ∈ frontier D, ν (baseEquiv (e (chart (i : M) p))) =
        profilePreferred (realBoundaryProfile (A.phaseRealChartMap i e.symm W) z
          (baseEquiv (e (chart (i : M) p))))) →
      (∀ k p, p ∈ (curves k).carrier → p ∈ D →
        let q := baseEquiv (e (chart (i : M) p))
        realSecondForm (A.phaseRealChartMap i e.symm W) (v k q) (v k q) q ≠ 0 ∧
        ν q ≠ -normalize (realSecondForm (A.phaseRealChartMap i e.symm W) (v k q) (v k q) q)) →
      ∃ N : PreferredNormal W,
        (∀ k p, p ∈ (curves k).carrier → (curves k).second W p ≠ 0 ∧
          spaceCoordinates (N.vector p) ≠ -normalize ((curves k).second W p)) ∧
        ∀ p ∈ E, (p ∈ D → N.vector p = A.phaseNormalLift i e ν p) ∧
          (p ∉ D → N.vector p = A.unitProjectedNormalField W n.vector p) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
