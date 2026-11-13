-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_anchored_atlas_phases
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_phases
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:45.028942+00:00
-- url     : https://prove2.me/theorems/01a6a353-6e59-46b5-8850-19038d49d7dc
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_phases: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_phases` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/AnchoredAtlasPhases.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/AnchoredAtlasPhases.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators`, `open JetPolynomial JetPolynomial.Perturbation RealModes WeightedEstimates PhaseGeometry PhaseGrid`):
--
--   ```lean
--   theorem anchored_atlas_phases (g : SmoothMetric M)
--       (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
--       (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
--       ∃ phaseStock : Finset PhaseBasis, ∃ weightStock : Finset ℝ,
--       ∃ z₀ K C ε W κ : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < K ∧ 1 ≤ C ∧
--         0 < ε ∧ 0 < W ∧ 0 < κ ∧
--       ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
--         ContMDiff planeModel spaceModel ∞ F →
--         (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
--         (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
--           ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
--           c ≤ NormalFrame.gramDet
--             (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
--             (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
--           b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
--       ∃ (s : A.centers → Finset Index) (P : ∀ i, (s i) → PhaseBasis)
--         (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
--         (w : AtlasCellPhase (ι := A.centers) → ℝ),
--         (∀ i a, P i a ∈ phaseStock) ∧ (∀ a, w a ∈ weightStock) ∧
--         (∑ i, ((s i).card : ℝ)) ≤ K/z^12 ∧
--         (∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion (s i) (z^6)) ∧
--         (∀ i a j, ξ (i,a.val,j) = (P i a).ξ j ∧
--           ‖(P i a).ξ j‖ ≤ C ∧ ‖(P i a).Q j‖ ≤ C) ∧
--         (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
--         (∀ G, A.ReadJetBall z F G → ∀ i (a : s i) x,
--           x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
--           x ∈ tsupport (cutoff (z^6) a.val) →
--           c/4 ≤ NormalFrame.gramDet
--             (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x).1
--             (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x).2 ∧
--           b/2 ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ∧ ∀ j,
--             ε/2 ≤ (P i a).Q j (A.tensorPlaneRead i g.inner x) ∧
--             (ε/4)*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ≤
--               ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x)
--                 (-((P i a).ξ j).2,((P i a).ξ j).1)‖ ∧
--             Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x) ((P i a).ξ j)) ∧
--         (∀ G, A.ReadJetBall z F G →
--           AtlasPairMargins (fun i : A.centers => (i : M)) A.weight s (z^6) κ ξ w G)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.AtlasCellPhase`, `OAI.ClosedSurfaceR4.AtlasPairMargins`, `OAI.ClosedSurfaceR4.PhaseGrid.Index`, `OAI.ClosedSurfaceR4.PhaseGrid.coverRegion` and `OAI.ClosedSurfaceR4.PhaseGrid.cutoff` (definitions bundle `OAIQ249SI000` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.PhaseGeometry.Good`, `OAI.ClosedSurfaceR4.PhaseGeometry.secondQuadratic`, `OAI.ClosedSurfaceR4.PhaseGrid.Base`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.RealModes.TangentPair` and `OAI.ClosedSurfaceR4.RealModes.firstJetPair` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.ReadJetBall` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_increment` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/AnchoredAtlasPhases.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_phases)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
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
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes WeightedEstimates PhaseGeometry PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem anchored_atlas_phases (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ phaseStock : Finset PhaseBasis, ∃ weightStock : Finset ℝ,
    ∃ z₀ K C ε W κ : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < K ∧ 1 ≤ C ∧
      0 < ε ∧ 0 < W ∧ 0 < κ ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
    ∃ (s : A.centers → Finset Index) (P : ∀ i, (s i) → PhaseBasis)
      (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
      (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ i a, P i a ∈ phaseStock) ∧ (∀ a, w a ∈ weightStock) ∧
      (∑ i, ((s i).card : ℝ)) ≤ K/z^12 ∧
      (∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion (s i) (z^6)) ∧
      (∀ i a j, ξ (i,a.val,j) = (P i a).ξ j ∧
        ‖(P i a).ξ j‖ ≤ C ∧ ‖(P i a).Q j‖ ≤ C) ∧
      (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
      (∀ G, A.ReadJetBall z F G → ∀ i (a : s i) x,
        x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        x ∈ tsupport (cutoff (z^6) a.val) →
        c/4 ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x).2 ∧
        b/2 ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ∧ ∀ j,
          ε/2 ≤ (P i a).Q j (A.tensorPlaneRead i g.inner x) ∧
          (ε/4)*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ≤
            ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x)
              (-((P i a).ξ j).2,((P i a).ξ j).1)‖ ∧
          Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x) ((P i a).ξ j)) ∧
      (∀ G, A.ReadJetBall z F G →
        AtlasPairMargins (fun i : A.centers => (i : M)) A.weight s (z^6) κ ξ w G) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
