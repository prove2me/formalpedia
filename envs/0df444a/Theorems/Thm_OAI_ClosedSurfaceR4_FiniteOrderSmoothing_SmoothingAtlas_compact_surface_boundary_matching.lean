-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_compact_surface_boundary_matching
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_boundary_matching
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:51:43.830866+00:00
-- url     : https://prove2.me/theorems/fe81cad8-4943-4b74-af3e-acbc85982280
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_boundary_matching: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_boundary_matching` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/SurfaceBoundaryMatching.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/SurfaceBoundaryMatching.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open JetPolynomial SurfaceJetCoordinates RealModes SmallModes GeometryPreservation VelocityFrame`):
--
--   ```lean
--   theorem compact_surface_boundary_matching
--       {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
--       (n : PreferredNormal F)
--       (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
--       (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
--       (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
--       {C : Set M} (hC : IsCompact C)
--       (hCs : C ⊆ ((chart (i : M)).trans e).source)
--       (hw : ∀ p ∈ C, A.weight i p ≠ 0)
--       (v : SmallModes.Base → SmallModes.Base) (hv : Continuous v)
--       (hB : ∀ p ∈ C, realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
--         (baseEquiv (e (chart (i : M) p))) ≠ 0)
--       (havoid : ∀ p ∈ C, spaceCoordinates (n.vector p) ≠
--         -normalize (realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
--           (baseEquiv (e (chart (i : M) p)))))
--       (hpositive : ∀ p ∈ C,
--         let q := baseEquiv (e (chart (i : M) p))
--         0 < realSecondForm (A.phaseRealChartMap i e.symm F) (v q) (v q) q ⬝ᵥ
--           spaceCoordinates (n.vector p))
--       (hcross : ∀ p ∈ C,
--         let q := baseEquiv (e (chart (i : M) p))
--         let H := A.phaseRealChartMap i e.symm F
--         0 < orderedCrossing H dy (v q) q
--           (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy) q)) :
--       ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
--         ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
--         ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
--         A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
--         ∀ O : Set M, (∀ y ∈ O, V =ᶠ[𝓝 y] G) → ∀ p ∈ C ∩ closure O, ∀ z : ℝ,
--         let q := baseEquiv (e (chart (i : M) p))
--         let H := A.phaseRealChartMap i e.symm W
--         0 < realSecondForm H (v q) (v q) q ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField W n.vector p) ∧
--         0 < realSecondForm H (v q) (v q) q ⬝ᵥ profilePreferred (realBoundaryProfile H z q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base` and `OAI.ClosedSurfaceR4.NormalFrame.Vec` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PreferredNormal` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realMetric`, `OAI.ClosedSurfaceR4.RealModes.realSecondForm`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv` and `OAI.ClosedSurfaceR4.VelocityFrame.normalize` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.GeometryPreservation.profilePreferred`, `OAI.ClosedSurfaceR4.GeometryPreservation.realBoundaryProfile` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.unitProjectedNormalField` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.RealModes.coordinateGaussianCurvature`, `OAI.ClosedSurfaceR4.VelocityFrame.orderedCrossing` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseRealChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.geometric_normal_extension` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/SurfaceBoundaryMatching.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_boundary_matching)

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
import Definitions.Def_OAIQ249SI006
import Definitions.Def_OAIQ249SI007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes GeometryPreservation VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem compact_surface_boundary_matching
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {C : Set M} (hC : IsCompact C)
    (hCs : C ⊆ ((chart (i : M)).trans e).source)
    (hw : ∀ p ∈ C, A.weight i p ≠ 0)
    (v : SmallModes.Base → SmallModes.Base) (hv : Continuous v)
    (hB : ∀ p ∈ C, realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
      (baseEquiv (e (chart (i : M) p))) ≠ 0)
    (havoid : ∀ p ∈ C, spaceCoordinates (n.vector p) ≠
      -normalize (realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
        (baseEquiv (e (chart (i : M) p)))))
    (hpositive : ∀ p ∈ C,
      let q := baseEquiv (e (chart (i : M) p))
      0 < realSecondForm (A.phaseRealChartMap i e.symm F) (v q) (v q) q ⬝ᵥ
        spaceCoordinates (n.vector p))
    (hcross : ∀ p ∈ C,
      let q := baseEquiv (e (chart (i : M) p))
      let H := A.phaseRealChartMap i e.symm F
      0 < orderedCrossing H dy (v q) q
        (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy) q)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ y ∈ O, V =ᶠ[𝓝 y] G) → ∀ p ∈ C ∩ closure O, ∀ z : ℝ,
      let q := baseEquiv (e (chart (i : M) p))
      let H := A.phaseRealChartMap i e.symm W
      0 < realSecondForm H (v q) (v q) q ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField W n.vector p) ∧
      0 < realSecondForm H (v q) (v q) q ⬝ᵥ profilePreferred (realBoundaryProfile H z q) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
