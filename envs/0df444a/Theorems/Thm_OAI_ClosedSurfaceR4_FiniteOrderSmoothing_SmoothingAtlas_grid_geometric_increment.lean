-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_geometric_increment
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:42:13.581671+00:00
-- url     : https://prove2.me/theorems/5d0e3f13-9494-4155-b404-f34ca12c7435
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/GridGeometricIncrement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/GridGeometricIncrement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean`, `open PhaseGeometry PhaseGrid`):
--
--   ```lean
--   theorem grid_geometric_increment (g : SmoothMetric M) (V : Finset SmallModes.Base)
--       (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
--       {ε κ b a₀ C₀ H₀ K D : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
--       (ha₀ : 0 < a₀) (hC₀ : 0 ≤ C₀) (hH₀ : 0 ≤ H₀) (hK : 0 ≤ K) (hD : 0 < D)
--   :
--       ∃ r : ℝ, 0 < r ∧ ∀ (FJ Y : ℕ → ℝ → ℝ),
--       (∀ m, RealModes.HasPolynomialBound (FJ m)) →
--       (∀ m, RealModes.HasPolynomialBound (Y m)) →
--       (∀ m x, 1 ≤ x → 1 ≤ FJ m x) →
--       (∀ m x, 1 ≤ x → 1 ≤ Y m x) → ∀ q : ℕ,
--       ∃ e : ℕ, ∃ E : ℝ, ∃ P Q : ℕ → ℝ → ℝ, 1 ≤ E ∧
--         (∀ m, RealModes.HasPolynomialBound (P m)) ∧
--         (∀ m, RealModes.HasPolynomialBound (Q m)) ∧
--       ∀ z : ℝ, ∀ _hz : 0 < z, z ≤ 1 → ∀ a : A.centers → Finset Index,
--         (∑ i, ((a i).card : ℝ)) ≤ K/z^12 →
--         (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
--           coverRegion (a i) (z^6)) →
--       ∀ (Qb : ∀ i, (a i) → PhaseBasis)
--         (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
--         (w : AtlasCellPhase (ι := A.centers) → ℝ),
--         (∀ i k j, ξ (i,k.val,j) = (Qb i k).ξ j) → (∀ l, 1 ≤ w l) →
--         (∀ l : A.GridPhaseIndex a, w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V) →
--         (∀ i k j, ‖(Qb i k).Q j‖ ≤ C₀) →
--         (∀ i k j y, (Qb i k).Q j (A.tensorPlaneRead i g.inner y) ≤ H₀) →
--         (∀ i k j y, y ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
--           a₀ ≤ (Qb i k).Q j (A.tensorPlaneRead i g.inner y)) →
--       ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F),
--         (∀ l p, atlasActive (fun i : A.centers => (i : M)) A.weight a (z^6) l p →
--           atlasGram F (l.1 : M) p ≠ 0 ∧ atlasSecondTensor F (l.1 : M) p ≠ 0 ∧
--           ε*‖atlasSecondTensor F (l.1 : M) p‖ ≤
--             ‖secondQuadratic (atlasSecondTensor F (l.1 : M) p) (-(ξ l).2,(ξ l).1)‖) →
--         AtlasPairMargins (fun i : A.centers => (i : M)) A.weight a (z^6) κ ξ w F →
--         (∀ i y, y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
--           Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) y)) →
--         (∀ i y, y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
--           b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y‖) →
--         (∀ i y, y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
--           ‖(NormalFrame.gramDet
--             (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
--             (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i F) y))⁻¹‖ ≤ D) →
--         (∀ i k j y, y ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
--           Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
--             (w (i,k.val,j) • (Qb i k).ξ j) ∧
--           ‖secondQuadratic (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
--             (-(w (i,k.val,j) • (Qb i k).ξ j).2,(w (i,k.val,j) • (Qb i k).ξ j).1)‖⁻¹ ≤ D) →
--       ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
--         (∀ m, 2*D ≤ FJ m z⁻¹ ∧ C₀ ≤ FJ m z⁻¹) →
--         (∀ i k j m, ‖w (i,k.val,j) • (Qb i k).ξ j‖ ≤ FJ m z⁻¹ ∧
--           ∀ hξ : w (i,k.val,j) • (Qb i k).ξ j ≠ 0,
--             ‖(phaseEquiv (w (i,k.val,j) • (Qb i k).ξ j) hξ).symm.toContinuousLinearMap‖ ≤ FJ m z⁻¹) →
--         (∀ i m l, l ≤ m+3 → WeightedEstimates.WeightedBound univ 1 l
--           (FJ m z⁻¹/(s : ℝ)^(l-2)) (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
--         (τ/s) ≤ min 1 ((r-r/2)/(2*(E*(z⁻¹)^e))) →
--       ∀ f : ∀ y : M, CovariantTwoTensor y,
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--           (fun y => TotalSpace.mk' TensorFiber y (f y)) →
--         (∀ y v v', f y v v' = f y v' v) →
--         (∀ y, ‖A.tensorEncode f y-A.tensorEncode g.inner y‖ ≤ r/2) →
--         (∀ m, A.TensorWeightedBound s m (Y m z⁻¹) f) →
--       ∀ δ : ℝ, 0 < δ → δ ≤ τ →
--         ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
--           (∀ m, A.WeightedBound τ m (P m z⁻¹*(δ*τ)) U) ∧
--           (∀ m, A.TensorWeightedBound τ m (Q m z⁻¹*(δ*(τ/s)^(q+1)+δ^3/τ))
--             (inducedTensor (F+U)-inducedTensor F-δ^2 • f))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.AtlasCellPhase`, `OAI.ClosedSurfaceR4.AtlasPairMargins`, `OAI.ClosedSurfaceR4.atlasActive`, `OAI.ClosedSurfaceR4.PhaseGrid.Index`, `OAI.ClosedSurfaceR4.PhaseGrid.coverRegion` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cellChartCompact` (definitions bundle `OAIQ249SI000` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.HasPolynomialBound` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.atlasSecondTensor`, `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor`, `OAI.ClosedSurfaceR4.PhaseGeometry.Good`, `OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv`, `OAI.ClosedSurfaceR4.PhaseGeometry.secondQuadratic`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.atlasGram` (definitions bundle `OAIQ249SI009` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.GridPhaseIndex` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGeometricIncrementDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGeometricIncrementFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGeometricIncrementFiberSpace` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.gridPhaseLabel` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorEncode` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_increment` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/GridGeometricIncrement.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment)

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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGeometricIncrementFiberSpace
local instance gridGeometricIncrementDualAdd_r447673_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGeometricIncrementDualSmul
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridGeometricIncrementFiberNormed
local instance gridGeometricIncrementSectionNormed_r447673_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridGeometricIncrementSectionSpace_r447673_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance instDecidableEqGridPhaseIndex_4_r447673_1 {s : A.centers → Finset Index} : DecidableEq (A.GridPhaseIndex s) := Classical.decEq _
theorem grid_geometric_increment (g : SmoothMetric M) (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b a₀ C₀ H₀ K D : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (ha₀ : 0 < a₀) (hC₀ : 0 ≤ C₀) (hH₀ : 0 ≤ H₀) (hK : 0 ≤ K) (hD : 0 < D)
:
    ∃ r : ℝ, 0 < r ∧ ∀ (FJ Y : ℕ → ℝ → ℝ),
    (∀ m, RealModes.HasPolynomialBound (FJ m)) →
    (∀ m, RealModes.HasPolynomialBound (Y m)) →
    (∀ m x, 1 ≤ x → 1 ≤ FJ m x) →
    (∀ m x, 1 ≤ x → 1 ≤ Y m x) → ∀ q : ℕ,
    ∃ e : ℕ, ∃ E : ℝ, ∃ P Q : ℕ → ℝ → ℝ, 1 ≤ E ∧
      (∀ m, RealModes.HasPolynomialBound (P m)) ∧
      (∀ m, RealModes.HasPolynomialBound (Q m)) ∧
    ∀ z : ℝ, ∀ _hz : 0 < z, z ≤ 1 → ∀ a : A.centers → Finset Index,
      (∑ i, ((a i).card : ℝ)) ≤ K/z^12 →
      (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
        coverRegion (a i) (z^6)) →
    ∀ (Qb : ∀ i, (a i) → PhaseBasis)
      (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
      (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ i k j, ξ (i,k.val,j) = (Qb i k).ξ j) → (∀ l, 1 ≤ w l) →
      (∀ l : A.GridPhaseIndex a, w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V) →
      (∀ i k j, ‖(Qb i k).Q j‖ ≤ C₀) →
      (∀ i k j y, (Qb i k).Q j (A.tensorPlaneRead i g.inner y) ≤ H₀) →
      (∀ i k j y, y ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
        a₀ ≤ (Qb i k).Q j (A.tensorPlaneRead i g.inner y)) →
    ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F),
      (∀ l p, atlasActive (fun i : A.centers => (i : M)) A.weight a (z^6) l p →
        atlasGram F (l.1 : M) p ≠ 0 ∧ atlasSecondTensor F (l.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor F (l.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor F (l.1 : M) p) (-(ξ l).2,(ξ l).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight a (z^6) κ ξ w F →
      (∀ i y, y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) y)) →
      (∀ i y, y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y‖) →
      (∀ i y, y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i F) y))⁻¹‖ ≤ D) →
      (∀ i k j y, y ∈ (modeSupport (A.cellChartCompact i (a i) (z^6) k.val) : Set SmallModes.Base) →
        Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
          (w (i,k.val,j) • (Qb i k).ξ j) ∧
        ‖secondQuadratic (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y)
          (-(w (i,k.val,j) • (Qb i k).ξ j).2,(w (i,k.val,j) • (Qb i k).ξ j).1)‖⁻¹ ≤ D) →
    ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, 2*D ≤ FJ m z⁻¹ ∧ C₀ ≤ FJ m z⁻¹) →
      (∀ i k j m, ‖w (i,k.val,j) • (Qb i k).ξ j‖ ≤ FJ m z⁻¹ ∧
        ∀ hξ : w (i,k.val,j) • (Qb i k).ξ j ≠ 0,
          ‖(phaseEquiv (w (i,k.val,j) • (Qb i k).ξ j) hξ).symm.toContinuousLinearMap‖ ≤ FJ m z⁻¹) →
      (∀ i m l, l ≤ m+3 → WeightedEstimates.WeightedBound univ 1 l
        (FJ m z⁻¹/(s : ℝ)^(l-2)) (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (τ/s) ≤ min 1 ((r-r/2)/(2*(E*(z⁻¹)^e))) →
    ∀ f : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (f y)) →
      (∀ y v v', f y v v' = f y v' v) →
      (∀ y, ‖A.tensorEncode f y-A.tensorEncode g.inner y‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (Y m z⁻¹) f) →
    ∀ δ : ℝ, 0 < δ → δ ≤ τ →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m (P m z⁻¹*(δ*τ)) U) ∧
        (∀ m, A.TensorWeightedBound τ m (Q m z⁻¹*(δ*(τ/s)^(q+1)+δ^3/τ))
          (inducedTensor (F+U)-inducedTensor F-δ^2 • f)) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
