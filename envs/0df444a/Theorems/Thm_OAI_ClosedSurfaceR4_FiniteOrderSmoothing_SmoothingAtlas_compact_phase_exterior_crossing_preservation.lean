-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_compact_phase_exterior_crossing_preservation
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_phase_exterior_crossing_preservation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:54:36.227861+00:00
-- url     : https://prove2.me/theorems/e403e485-554e-4df9-bdbb-16cf7fe09953
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_phase_exterior_crossing_preservation (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_phase_exterior_crossing_preservation` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/PhaseExteriorPreservation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/PhaseExteriorPreservation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open JetPolynomial SurfaceJetCoordinates RealModes SmallModes GeometryPreservation VelocityFrame`):
--
--   ```lean
--   theorem compact_phase_exterior_crossing_preservation {F : M → Space}
--       (hF : ContMDiff planeModel spaceModel ∞ F)
--       (hI : ∀ p, Function.Injective (surfaceDifferential F p)) (n : PreferredNormal F)
--       (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
--       (i : B.centers) {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
--       {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S))
--       {p : X → M} {q : X → JetPolynomial.Base} (hp : Continuous p) (hq : Continuous q)
--       (O : Set M) (P : Set JetPolynomial.Base)
--       (hP : ∀ y ∈ P, T y ∈ (chart (i : M)).target)
--       (hPO : ∀ y ∈ P, (chart (i : M)).symm (T y) ∈ O)
--       (hpO : ∀ x, p x ∈ closure O) (hqP : ∀ x, q x ∈ closure P ∩ S)
--       (hD : ∀ x, NormalFrame.gramDet
--         (coordDeriv dx (B.phaseRealChartMap i T F) (baseEquiv (q x)))
--         (coordDeriv dy (B.phaseRealChartMap i T F) (baseEquiv (q x))) ≠ 0)
--       {v w : X → SmallModes.Base} (hv : Continuous v) (hw : Continuous w)
--       (hpositive : ∀ x,
--         0 < realSecondForm (B.phaseRealChartMap i T F) (v x) (v x)
--           (baseEquiv (q x)) ⬝ᵥ spaceCoordinates (n.vector (p x)) ∧
--         0 < realSecondForm (B.phaseRealChartMap i T F) (w x) (w x)
--           (baseEquiv (q x)) ⬝ᵥ spaceCoordinates (n.vector (p x)))
--       (hcross : ∀ x,
--         0 < orderedCrossing (B.phaseRealChartMap i T F) (v x) (w x)
--           (baseEquiv (q x)) (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap i T F) dx dx)
--           (realMetric (B.phaseRealChartMap i T F) dx dy)
--           (realMetric (B.phaseRealChartMap i T F) dy dy)
--           (baseEquiv (q x))) ∧
--         0 < orderedCrossing (B.phaseRealChartMap i T F) (w x) (v x)
--           (baseEquiv (q x)) (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap i T F) dx dx)
--           (realMetric (B.phaseRealChartMap i T F) dx dy)
--           (realMetric (B.phaseRealChartMap i T F) dy dy)
--           (baseEquiv (q x)))) :
--       ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
--         ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
--         ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
--         A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
--         (∀ y ∈ O, V =ᶠ[𝓝 y] G) →
--         ∀ x : X,
--         (0 < realSecondForm (B.phaseRealChartMap i T W) (v x) (v x)
--           (baseEquiv (q x)) ⬝ᵥ
--             spaceCoordinates (A.unitProjectedNormalField W n.vector (p x)) ∧
--          0 < realSecondForm (B.phaseRealChartMap i T W) (w x) (w x)
--           (baseEquiv (q x)) ⬝ᵥ
--             spaceCoordinates (A.unitProjectedNormalField W n.vector (p x))) ∧
--         (0 < orderedCrossing (B.phaseRealChartMap i T W) (v x) (w x)
--           (baseEquiv (q x)) (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap i T W) dx dx)
--           (realMetric (B.phaseRealChartMap i T W) dx dy)
--           (realMetric (B.phaseRealChartMap i T W) dy dy)
--           (baseEquiv (q x))) ∧
--          0 < orderedCrossing (B.phaseRealChartMap i T W) (w x) (v x)
--           (baseEquiv (q x)) (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap i T W) dx dx)
--           (realMetric (B.phaseRealChartMap i T W) dx dy)
--           (realMetric (B.phaseRealChartMap i T W) dy dy)
--           (baseEquiv (q x))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.surfaceDifferential`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.NormalFrame.Vec` and `OAI.ClosedSurfaceR4.NormalFrame.gramDet` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PreferredNormal` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realMetric`, `OAI.ClosedSurfaceR4.RealModes.realSecondForm`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy` and `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.unitProjectedNormalField` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.RealModes.coordinateGaussianCurvature`, `OAI.ClosedSurfaceR4.VelocityFrame.orderedCrossing` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseRealChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_circular_primitive_boundary_step` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/PhaseExteriorPreservation.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_phase_exterior_crossing_preservation)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
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
variable {M X : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [TopologicalSpace X] [CompactSpace X]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem compact_phase_exterior_crossing_preservation {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p)) (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : B.centers) {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S))
    {p : X → M} {q : X → JetPolynomial.Base} (hp : Continuous p) (hq : Continuous q)
    (O : Set M) (P : Set JetPolynomial.Base)
    (hP : ∀ y ∈ P, T y ∈ (chart (i : M)).target)
    (hPO : ∀ y ∈ P, (chart (i : M)).symm (T y) ∈ O)
    (hpO : ∀ x, p x ∈ closure O) (hqP : ∀ x, q x ∈ closure P ∩ S)
    (hD : ∀ x, NormalFrame.gramDet
      (coordDeriv dx (B.phaseRealChartMap i T F) (baseEquiv (q x)))
      (coordDeriv dy (B.phaseRealChartMap i T F) (baseEquiv (q x))) ≠ 0)
    {v w : X → SmallModes.Base} (hv : Continuous v) (hw : Continuous w)
    (hpositive : ∀ x,
      0 < realSecondForm (B.phaseRealChartMap i T F) (v x) (v x)
        (baseEquiv (q x)) ⬝ᵥ spaceCoordinates (n.vector (p x)) ∧
      0 < realSecondForm (B.phaseRealChartMap i T F) (w x) (w x)
        (baseEquiv (q x)) ⬝ᵥ spaceCoordinates (n.vector (p x)))
    (hcross : ∀ x,
      0 < orderedCrossing (B.phaseRealChartMap i T F) (v x) (w x)
        (baseEquiv (q x)) (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap i T F) dx dx)
        (realMetric (B.phaseRealChartMap i T F) dx dy)
        (realMetric (B.phaseRealChartMap i T F) dy dy)
        (baseEquiv (q x))) ∧
      0 < orderedCrossing (B.phaseRealChartMap i T F) (w x) (v x)
        (baseEquiv (q x)) (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap i T F) dx dx)
        (realMetric (B.phaseRealChartMap i T F) dx dy)
        (realMetric (B.phaseRealChartMap i T F) dy dy)
        (baseEquiv (q x)))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      (∀ y ∈ O, V =ᶠ[𝓝 y] G) →
      ∀ x : X,
      (0 < realSecondForm (B.phaseRealChartMap i T W) (v x) (v x)
        (baseEquiv (q x)) ⬝ᵥ
          spaceCoordinates (A.unitProjectedNormalField W n.vector (p x)) ∧
       0 < realSecondForm (B.phaseRealChartMap i T W) (w x) (w x)
        (baseEquiv (q x)) ⬝ᵥ
          spaceCoordinates (A.unitProjectedNormalField W n.vector (p x))) ∧
      (0 < orderedCrossing (B.phaseRealChartMap i T W) (v x) (w x)
        (baseEquiv (q x)) (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap i T W) dx dx)
        (realMetric (B.phaseRealChartMap i T W) dx dy)
        (realMetric (B.phaseRealChartMap i T W) dy dy)
        (baseEquiv (q x))) ∧
       0 < orderedCrossing (B.phaseRealChartMap i T W) (w x) (v x)
        (baseEquiv (q x)) (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap i T W) dx dx)
        (realMetric (B.phaseRealChartMap i T W) dx dy)
        (realMetric (B.phaseRealChartMap i T W) dy dy)
        (baseEquiv (q x)))) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
