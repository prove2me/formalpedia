-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_anchored_smoothed_increment
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_smoothed_increment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:38:25.285031+00:00
-- url     : https://prove2.me/theorems/074e3dda-e753-4e45-a87c-ce4bb22b6457
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_smoothed_increment: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_smoothed_increment` of [lean/OAI/Geometry/SurfaceImmersion/Correction/AnchoredSmoothedIncrement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AnchoredSmoothedIncrement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry`):
--
--   ```lean
--   theorem anchored_smoothed_increment (g : SmoothMetric M)
--       (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
--       (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
--       ∃ z₀ a D : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧
--       ∀ (r q : ℕ) (Budget : ℝ → ℝ), HasPolynomialBound Budget →
--       ∃ e : ℕ, ∃ E : ℝ, ∃ P Q : ℕ → ℝ → ℝ, 1 ≤ E ∧
--         (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (Q m)) ∧
--       ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
--         ContMDiff planeModel spaceModel ∞ F →
--         (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
--         (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
--           ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
--           c ≤ NormalFrame.gramDet
--             (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
--             (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
--           b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
--       ∀ (G : M → Space) (H : ∀ y : M, CovariantTwoTensor y),
--         ContMDiff planeModel spaceModel ∞ G →
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--           (fun y => TotalSpace.mk' TensorFiber y (H y)) →
--         (∀ y v w, H y v w = H y w v) →
--       ∀ t s : ℝ, 0 < t → t ≤ 1 → 0 < s → s ≤ 1 →
--         A.InputBound t r (Budget z⁻¹) G H →
--         A.WeightedBound 1 2 (z^4/D) (A.smooth r s G-F) →
--       ∀ δ δ' τ : ℝ, 0 < δ → 0 ≤ δ' → δ' ≤ δ → 0 < τ → τ ≤ s → δ ≤ τ →
--         τ/s ≤ min 1 ((a-a/2)/(2*(E*(z⁻¹)^e))) →
--         (∀ y, ‖A.tensorEncode (A.tensorSmooth r s H-(δ'/δ)^2 • g.inner) y-
--           A.tensorEncode g.inner y‖ ≤ a/2) →
--         ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
--           (∀ m, A.WeightedBound τ m (P m z⁻¹*(δ*τ)) U) ∧
--           (∀ m, A.TensorWeightedBound τ m (Q m z⁻¹*(δ*(τ/s)^(q+1)+δ^3/τ))
--             (realizedTensorError g.inner (A.tensorSmooth r s H) δ δ' (A.smooth r s G) U))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.HasPolynomialBound` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.smooth` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.RealModes.TangentPair` and `OAI.ClosedSurfaceR4.RealModes.firstJetPair` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.realizedTensorError` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredSmoothDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredSmoothFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredSmoothFiberSpace` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.InputBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorEncode` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_actual_step` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AnchoredSmoothedIncrement.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_smoothed_increment)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
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
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredSmoothFiberSpace
local instance anchoredSmoothDualAdd_r861371_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredSmoothDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredSmoothFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredSmoothSectionNormed
local instance anchoredSmoothSectionSpace_r861371_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem anchored_smoothed_increment (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ z₀ a D : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧
    ∀ (r q : ℕ) (Budget : ℝ → ℝ), HasPolynomialBound Budget →
    ∃ e : ℕ, ∃ E : ℝ, ∃ P Q : ℕ → ℝ → ℝ, 1 ≤ E ∧
      (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (Q m)) ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
    ∀ (G : M → Space) (H : ∀ y : M, CovariantTwoTensor y),
      ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (H y)) →
      (∀ y v w, H y v w = H y w v) →
    ∀ t s : ℝ, 0 < t → t ≤ 1 → 0 < s → s ≤ 1 →
      A.InputBound t r (Budget z⁻¹) G H →
      A.WeightedBound 1 2 (z^4/D) (A.smooth r s G-F) →
    ∀ δ δ' τ : ℝ, 0 < δ → 0 ≤ δ' → δ' ≤ δ → 0 < τ → τ ≤ s → δ ≤ τ →
      τ/s ≤ min 1 ((a-a/2)/(2*(E*(z⁻¹)^e))) →
      (∀ y, ‖A.tensorEncode (A.tensorSmooth r s H-(δ'/δ)^2 • g.inner) y-
        A.tensorEncode g.inner y‖ ≤ a/2) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m (P m z⁻¹*(δ*τ)) U) ∧
        (∀ m, A.TensorWeightedBound τ m (Q m z⁻¹*(δ*(τ/s)^(q+1)+δ^3/τ))
          (realizedTensorError g.inner (A.tensorSmooth r s H) δ δ' (A.smooth r s G) U)) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
