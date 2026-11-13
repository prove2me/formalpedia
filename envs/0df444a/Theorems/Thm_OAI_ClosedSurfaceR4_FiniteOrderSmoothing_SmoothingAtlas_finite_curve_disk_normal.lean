-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_curve_disk_normal
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_curve_disk_normal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:32:51.230672+00:00
-- url     : https://prove2.me/theorems/f036b5ae-7719-410d-b425-22bf3feb2690
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_curve_disk_normal: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_curve_disk_normal` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/SurfaceCurveNormalGluing.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/SurfaceCurveNormalGluing.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open JetPolynomial SurfaceJetCoordinates RealModes SmallModes NormalFrame VelocityFrame`):
--
--   ```lean
--   theorem finite_curve_disk_normal
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
--       (E : Set M) (hE : E.Finite) (hEf : Disjoint E (frontier D)) :
--       ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
--         ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
--         ∀ h : SmoothMetric M, IsSmoothIsometricImmersion M h W →
--         ∀ b d : ℝ, 0 ≤ b → 0 ≤ d → b+d < ρ →
--         A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 d (W-V) →
--         (∀ p ∉ closure D, V =ᶠ[𝓝 p] G) →
--         ∀ U₀ : Set SmallModes.Base, IsOpen U₀ → ∀ ν : SmallModes.Base → Vec,
--         ContDiffOn ℝ ∞ ν U₀ →
--         (∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1) →
--         (∀ x ∈ U₀, ∀ v : SmallModes.Base,
--           SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm W) x ⬝ᵥ ν x = 0) →
--         MapsTo (fun p => baseEquiv (e (chart (i : M) p))) (closure D) U₀ →
--         (∀ p ∈ frontier D, spaceCoordinates (A.unitProjectedNormalField W n.vector p) ≠
--           -ν (baseEquiv (e (chart (i : M) p)))) →
--         (∀ k p, p ∈ (curves k).carrier → p ∈ D →
--           (curves k).second W p ≠ 0 ∧
--           ν (baseEquiv (e (chart (i : M) p))) ≠ -normalize ((curves k).second W p)) →
--         (∀ k p, p ∈ (curves k).carrier → p ∈ frontier D →
--           0 < (curves k).second W p ⬝ᵥ ν (baseEquiv (e (chart (i : M) p))) ∧
--           0 < (curves k).second W p ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField W n.vector p)) →
--         ∃ N : PreferredNormal W,
--           (∀ k p, p ∈ (curves k).carrier → (curves k).second W p ≠ 0 ∧
--             spaceCoordinates (N.vector p) ≠ -normalize ((curves k).second W p)) ∧
--           ∀ p ∈ E, (p ∈ D → N.vector p = A.phaseNormalLift i e ν p) ∧
--             (p ∉ D → N.vector p = A.unitProjectedNormalField W n.vector p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base` and `OAI.ClosedSurfaceR4.NormalFrame.Vec` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PreferredNormal` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv` and `OAI.ClosedSurfaceR4.VelocityFrame.normalize` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.unitProjectedNormalField` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseNormalLift` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.second` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseRealChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.geometric_normal_extension` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/SurfaceCurveNormalGluing.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_curve_disk_normal)

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
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes NormalFrame VelocityFrame
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [Fintype κ]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem finite_curve_disk_normal
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
    (E : Set M) (hE : E.Finite) (hEf : Disjoint E (frontier D)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ∀ h : SmoothMetric M, IsSmoothIsometricImmersion M h W →
      ∀ b d : ℝ, 0 ≤ b → 0 ≤ d → b+d < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 d (W-V) →
      (∀ p ∉ closure D, V =ᶠ[𝓝 p] G) →
      ∀ U₀ : Set SmallModes.Base, IsOpen U₀ → ∀ ν : SmallModes.Base → Vec,
      ContDiffOn ℝ ∞ ν U₀ →
      (∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1) →
      (∀ x ∈ U₀, ∀ v : SmallModes.Base,
        SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm W) x ⬝ᵥ ν x = 0) →
      MapsTo (fun p => baseEquiv (e (chart (i : M) p))) (closure D) U₀ →
      (∀ p ∈ frontier D, spaceCoordinates (A.unitProjectedNormalField W n.vector p) ≠
        -ν (baseEquiv (e (chart (i : M) p)))) →
      (∀ k p, p ∈ (curves k).carrier → p ∈ D →
        (curves k).second W p ≠ 0 ∧
        ν (baseEquiv (e (chart (i : M) p))) ≠ -normalize ((curves k).second W p)) →
      (∀ k p, p ∈ (curves k).carrier → p ∈ frontier D →
        0 < (curves k).second W p ⬝ᵥ ν (baseEquiv (e (chart (i : M) p))) ∧
        0 < (curves k).second W p ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField W n.vector p)) →
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
