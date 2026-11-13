-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_free_forced_increment
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_forced_increment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:40:32.383207+00:00
-- url     : https://prove2.me/theorems/9b5e428d-2225-4a59-888a-e9a50ce61d51
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_forced_increment: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_forced_increment` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/GridIncrementProfile.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/GridIncrementProfile.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean`, `open PhaseGeometry PhaseGrid`):
--
--   ```lean
--   theorem grid_free_forced_increment (V : Finset SmallModes.Base)
--       (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
--       {ε κ b D₀ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
--       (FJ C J N B : ℕ → ℝ → ℝ)
--       (hFJ : ∀ m, RealModes.HasPolynomialBound (FJ m))
--       (hFJ1 : ∀ m x, 1 ≤ x → 1 ≤ FJ m x)
--       (hC : ∀ m, RealModes.HasPolynomialBound (C m))
--       (hJ : ∀ m, RealModes.HasPolynomialBound (J m))
--       (hN : ∀ m, RealModes.HasPolynomialBound (N m))
--       (hB : ∀ m, RealModes.HasPolynomialBound (B m))
--       (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x)
--       (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
--       ∃ α β γ ζ : ℕ → ℝ → ℝ, ∃ D : ℕ → ℝ,
--         (∀ m, RealModes.HasPolynomialBound (α m)) ∧
--         (∀ m, RealModes.HasPolynomialBound (β m)) ∧
--         (∀ m, RealModes.HasPolynomialBound (γ m)) ∧
--         (∀ m, RealModes.HasPolynomialBound (ζ m)) ∧ (∀ m, 0 ≤ D m) ∧
--         ∀ (h : ℝ) (a : A.centers → Finset Index)
--           (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
--           (w : AtlasCellPhase (ι := A.centers) → ℝ),
--         (∀ l, 1 ≤ w l) →
--         (∀ l : A.GridPhaseIndex a, w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V) →
--         ∀ n : ℕ, Fintype.card (A.GridPhaseIndex a) ≤ n → ∀ x : ℝ, 1 ≤ x →
--         ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F),
--         (∀ l p, atlasActive (fun i : A.centers => (i : M)) A.weight a h l p →
--           atlasGram F (l.1 : M) p ≠ 0 ∧ atlasSecondTensor F (l.1 : M) p ≠ 0 ∧
--           ε*‖atlasSecondTensor F (l.1 : M) p‖ ≤
--             ‖secondQuadratic (atlasSecondTensor F (l.1 : M) p) (-(ξ l).2,(ξ l).1)‖) →
--         AtlasPairMargins (fun i : A.centers => (i : M)) A.weight a h κ ξ w F →
--         (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
--           Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
--         (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
--           b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
--         (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
--           ‖(NormalFrame.gramDet
--             (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
--             (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D₀) →
--         ∀ {φ : ∀ i, ((a i) × Fin 3) → JetPolynomial.Base → ℝ}
--           {τ : ℝ} {s : ℝ≥0}
--           {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
--             (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j)
--             (A.cellChartCompact i (a i) h j.1.val) τ s}
--           {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
--           (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
--         (∀ i j, φ i j = phaseLinear (w (i,j.1.val,j.2) • ξ (i,j.1.val,j.2)) ∘
--           planeCoordinateIsometry) →
--         (∀ i j, (c i j).C = (fun m => C m x) ∧ (c i j).J = (fun m => J m x) ∧
--           ∀ m, (c i j).D m = 0) →
--         ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
--         (∀ m, ρ⁻¹ ≤ B m x) →
--         (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.forms m ≤ B m x ∧
--           (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ N m x) →
--         (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
--           (FJ m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
--         ∀ δ : ℝ, 0 < δ → δ ≤ τ → ∀ u : ∀ y : M, CovariantTwoTensor y,
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--           (fun y => TotalSpace.mk' TensorFiber y (u y)) →
--         (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
--         (∀ i m, WeightedEstimates.WeightedBound univ s m (B m x) (A.tensorPlaneRead i u)) →
--         ∀ H : ∀ y : M, CovariantTwoTensor y,
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--           (fun y => TotalSpace.mk' TensorFiber y (H y)) →
--         ∀ Rm : ℕ → ℝ,
--         (∀ m, A.TensorWeightedBound τ m (Rm m)
--           (A.finiteAtlasFreeMean d hρ δ q u-δ^2 • H)) →
--         ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
--           (∀ m, A.WeightedBound τ m
--             ((α m x*(n : ℝ)+β m x*((n : ℝ)+2*(n : ℝ)^2))*(δ*τ)) U) ∧
--           (∀ m, A.TensorWeightedBound τ m
--             ((τ/s)^(q+1)*(ζ m x*(n : ℝ)*(δ*τ)+γ m x*((n : ℝ)+2*(n : ℝ)^2)*δ^2)+Rm m+
--               D m*(2*(α (m+1) x*(n : ℝ))*(β (m+1) x*((n : ℝ)+2*(n : ℝ)^2))+
--                 (β (m+1) x*((n : ℝ)+2*(n : ℝ)^2))^2)*(δ^3/τ))
--             (inducedTensor (F+U)-inducedTensor F-δ^2 • H))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.AtlasCellPhase`, `OAI.ClosedSurfaceR4.AtlasPairMargins`, `OAI.ClosedSurfaceR4.atlasActive`, `OAI.ClosedSurfaceR4.PhaseGrid.Index` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cellChartCompact` (definitions bundle `OAIQ249SI000` of this split); `OAI.ClosedSurfaceR4.FiniteMean.InTrialBall`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.HasPolynomialBound` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.atlasSecondTensor`, `OAI.ClosedSurfaceR4.phaseLinear`, `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor`, `OAI.ClosedSurfaceR4.PhaseGeometry.secondQuadratic`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx`, `OAI.ClosedSurfaceR4.SmallModes.dy`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap_smooth` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.emptyMetricPolynomial`, `OAI.ClosedSurfaceR4.PhaseMean.Budgets`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.chartCompact` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.realMap` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.atlasGram` (definitions bundle `OAIQ249SI009` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.GridPhaseIndex` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridIncrementProfileDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridIncrementProfileFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridIncrementProfileFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasFreeMean` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.gridPhaseLabel` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_adjusted_increment` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/GridIncrementProfile.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_forced_increment)

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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridIncrementProfileFiberSpace
local instance gridIncrementProfileDualAdd_r0d9312_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridIncrementProfileDualSmul
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridIncrementProfileFiberNormed
local instance gridIncrementProfileSectionNormed_r0d9312_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridIncrementProfileSectionSpace_r0d9312_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance instDecidableEqGridPhaseIndex_2_r0d9312_1 {s : A.centers → Finset Index} : DecidableEq (A.GridPhaseIndex s) := Classical.decEq _
theorem grid_free_forced_increment (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b D₀ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (FJ C J N B : ℕ → ℝ → ℝ)
    (hFJ : ∀ m, RealModes.HasPolynomialBound (FJ m))
    (hFJ1 : ∀ m x, 1 ≤ x → 1 ≤ FJ m x)
    (hC : ∀ m, RealModes.HasPolynomialBound (C m))
    (hJ : ∀ m, RealModes.HasPolynomialBound (J m))
    (hN : ∀ m, RealModes.HasPolynomialBound (N m))
    (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x)
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
    ∃ α β γ ζ : ℕ → ℝ → ℝ, ∃ D : ℕ → ℝ,
      (∀ m, RealModes.HasPolynomialBound (α m)) ∧
      (∀ m, RealModes.HasPolynomialBound (β m)) ∧
      (∀ m, RealModes.HasPolynomialBound (γ m)) ∧
      (∀ m, RealModes.HasPolynomialBound (ζ m)) ∧ (∀ m, 0 ≤ D m) ∧
      ∀ (h : ℝ) (a : A.centers → Finset Index)
        (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
        (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ l, 1 ≤ w l) →
      (∀ l : A.GridPhaseIndex a, w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V) →
      ∀ n : ℕ, Fintype.card (A.GridPhaseIndex a) ≤ n → ∀ x : ℝ, 1 ≤ x →
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F),
      (∀ l p, atlasActive (fun i : A.centers => (i : M)) A.weight a h l p →
        atlasGram F (l.1 : M) p ≠ 0 ∧ atlasSecondTensor F (l.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor F (l.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor F (l.1 : M) p) (-(ξ l).2,(ξ l).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight a h κ ξ w F →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D₀) →
      ∀ {φ : ∀ i, ((a i) × Fin 3) → JetPolynomial.Base → ℝ}
        {τ : ℝ} {s : ℝ≥0}
        {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
          (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j)
          (A.cellChartCompact i (a i) h j.1.val) τ s}
        {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
        (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      (∀ i j, φ i j = phaseLinear (w (i,j.1.val,j.2) • ξ (i,j.1.val,j.2)) ∘
        planeCoordinateIsometry) →
      (∀ i j, (c i j).C = (fun m => C m x) ∧ (c i j).J = (fun m => J m x) ∧
        ∀ m, (c i j).D m = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, ρ⁻¹ ≤ B m x) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.forms m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ N m x) →
      (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (FJ m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ τ → ∀ u : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (u y)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i m, WeightedEstimates.WeightedBound univ s m (B m x) (A.tensorPlaneRead i u)) →
      ∀ H : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (H y)) →
      ∀ Rm : ℕ → ℝ,
      (∀ m, A.TensorWeightedBound τ m (Rm m)
        (A.finiteAtlasFreeMean d hρ δ q u-δ^2 • H)) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m
          ((α m x*(n : ℝ)+β m x*((n : ℝ)+2*(n : ℝ)^2))*(δ*τ)) U) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ/s)^(q+1)*(ζ m x*(n : ℝ)*(δ*τ)+γ m x*((n : ℝ)+2*(n : ℝ)^2)*δ^2)+Rm m+
            D m*(2*(α (m+1) x*(n : ℝ))*(β (m+1) x*((n : ℝ)+2*(n : ℝ)^2))+
              (β (m+1) x*((n : ℝ)+2*(n : ℝ)^2))^2)*(δ^3/τ))
          (inducedTensor (F+U)-inducedTensor F-δ^2 • H)) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
