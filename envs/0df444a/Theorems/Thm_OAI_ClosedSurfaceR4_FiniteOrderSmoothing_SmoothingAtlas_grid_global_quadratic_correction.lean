-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_global_quadratic_correction
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_global_quadratic_correction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:43:05.043816+00:00
-- url     : https://prove2.me/theorems/592d33fe-417e-4f48-af30-874171ba95df
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_global_quadratic_correction: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_global_quadratic_correction` of [lean/OAI/Geometry/SurfaceImmersion/Correction/GridGlobalQuadraticCorrection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/GridGlobalQuadraticCorrection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean`, `open PhaseGeometry PhaseGrid`):
--
--   ```lean
--   theorem grid_global_quadratic_correction (V : Finset SmallModes.Base)
--       (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
--       {ε κ b D₀ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
--       (B α β : ℕ → ℝ → ℝ)
--       (hB : ∀ m, RealModes.HasPolynomialBound (B m))
--       (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x)
--       (hα : ∀ m, RealModes.HasPolynomialBound (α m))
--       (hβ : ∀ m, RealModes.HasPolynomialBound (β m)) (q : ℕ) :
--       ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
--         ∀ (h : ℝ) (s₀ : A.centers → Finset Index)
--           (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
--           (w : AtlasCellPhase (ι := A.centers) → ℝ),
--         (∀ a, 1 ≤ w a) →
--         (∀ a : A.GridPhaseIndex s₀, w (A.gridPhaseLabel a) • ξ (A.gridPhaseLabel a) ∈ V) →
--         ∀ n : ℕ, Fintype.card (A.GridPhaseIndex s₀) ≤ n → ∀ x : ℝ, 1 ≤ x →
--         ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F),
--         (∀ a p, atlasActive (fun i : A.centers => (i : M)) A.weight s₀ h a p →
--           atlasGram F (a.1 : M) p ≠ 0 ∧ atlasSecondTensor F (a.1 : M) p ≠ 0 ∧
--           ε*‖atlasSecondTensor F (a.1 : M) p‖ ≤
--             ‖secondQuadratic (atlasSecondTensor F (a.1 : M) p) (-(ξ a).2,(ξ a).1)‖) →
--         AtlasPairMargins (fun i : A.centers => (i : M)) A.weight s₀ h κ ξ w F →
--         (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
--           Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
--         (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
--           b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
--         (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
--           ‖(NormalFrame.gramDet
--             (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
--             (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D₀) →
--         ∀ (τ δ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ δ →
--         (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
--           (B m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
--         ∀ (Z : A.GridPhaseIndex s₀ → M → Fin 4 → ℂ)
--           (_hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a)),
--         (∀ a, tsupport (Z a) ⊆ A.gridPhaseSupport h a) →
--         (∀ k a m, WeightedEstimates.WeightedBound univ s (m+1)
--           (α m x*(δ*τ)) (A.vectorPlaneRead k (Z a))) →
--         (∀ k a m v, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m
--           (β m x) (SmallModes.coordDeriv v (A.vectorPlaneRead k (A.gridRestoredPhase (s := s₀) ξ w a)))) →
--         ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
--           (∀ m, A.WeightedBound τ m (δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m))) W) ∧
--           (∀ m, A.TensorWeightedBound τ m
--             ((τ/s)^(q+1)*(δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m))))
--             (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
--               A.tensorPlaneRestore (fun k y => (A.planeWeight k y)^2 •
--                 RealModes.nonzeroPhaseSum τ
--                   (fun a => A.vectorPlaneRead k (A.gridRestoredPhase (s := s₀) ξ w a))
--                   (fun a => A.vectorPlaneRead k (Z a)) y)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.AtlasCellPhase`, `OAI.ClosedSurfaceR4.AtlasPairMargins`, `OAI.ClosedSurfaceR4.atlasActive` and `OAI.ClosedSurfaceR4.PhaseGrid.Index` (definitions bundle `OAIQ249SI000` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.HasPolynomialBound` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.atlasSecondTensor`, `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.PhaseGeometry.secondQuadratic`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Ambient`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.planeWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearMetricTensor` and `OAI.ClosedSurfaceR4.RealModes.nonzeroPhaseSum` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGlobalQuadraticDualAdd` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.atlasGram` (definitions bundle `OAIQ249SI009` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.GridPhaseIndex` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.gridPhaseLabel`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.gridPhaseSupport`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.gridRestoredPhase` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.instDecidableEqGridPhaseIndex` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_forced_increment` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/GridGlobalQuadraticCorrection.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_global_quadratic_correction)

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
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGlobalQuadraticDualAdd
local instance gridGlobalQuadraticFiberNormed_rdb9a82_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance gridGlobalQuadraticFiberSpace_rdb9a82_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance gridGlobalQuadraticDualSmul_rdb9a82_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid

local instance gridGlobalQuadraticSectionNormed_rdb9a82_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridGlobalQuadraticSectionSpace_rdb9a82_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.instDecidableEqGridPhaseIndex
theorem grid_global_quadratic_correction (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b D₀ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (B α β : ℕ → ℝ → ℝ)
    (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x)
    (hα : ∀ m, RealModes.HasPolynomialBound (α m))
    (hβ : ∀ m, RealModes.HasPolynomialBound (β m)) (q : ℕ) :
    ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
      ∀ (h : ℝ) (s₀ : A.centers → Finset Index)
        (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
        (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ a, 1 ≤ w a) →
      (∀ a : A.GridPhaseIndex s₀, w (A.gridPhaseLabel a) • ξ (A.gridPhaseLabel a) ∈ V) →
      ∀ n : ℕ, Fintype.card (A.GridPhaseIndex s₀) ≤ n → ∀ x : ℝ, 1 ≤ x →
      ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F),
      (∀ a p, atlasActive (fun i : A.centers => (i : M)) A.weight s₀ h a p →
        atlasGram F (a.1 : M) p ≠ 0 ∧ atlasSecondTensor F (a.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor F (a.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor F (a.1 : M) p) (-(ξ a).2,(ξ a).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight s₀ h κ ξ w F →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D₀) →
      ∀ (τ δ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ δ →
      (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (B m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
      ∀ (Z : A.GridPhaseIndex s₀ → M → Fin 4 → ℂ)
        (_hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a)),
      (∀ a, tsupport (Z a) ⊆ A.gridPhaseSupport h a) →
      (∀ k a m, WeightedEstimates.WeightedBound univ s (m+1)
        (α m x*(δ*τ)) (A.vectorPlaneRead k (Z a))) →
      (∀ k a m v, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m
        (β m x) (SmallModes.coordDeriv v (A.vectorPlaneRead k (A.gridRestoredPhase (s := s₀) ξ w a)))) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m))) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ/s)^(q+1)*(δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m))))
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k y => (A.planeWeight k y)^2 •
              RealModes.nonzeroPhaseSum τ
                (fun a => A.vectorPlaneRead k (A.gridRestoredPhase (s := s₀) ξ w a))
                (fun a => A.vectorPlaneRead k (Z a)) y))) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
