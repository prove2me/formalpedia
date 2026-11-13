-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_free_mean_residual
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_mean_residual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:40:11.543127+00:00
-- url     : https://prove2.me/theorems/1235931d-abc8-49fc-ab1c-f520bf7f0abe
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_mean_residual: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_mean_residual` of [lean/OAI/Geometry/SurfaceImmersion/Correction/GridFreeMeanIdentity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/GridFreeMeanIdentity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry`, `open PhaseGrid (Index coverRegion supportedCellCutoff)`):
--
--   ```lean
--   theorem grid_free_mean_residual
--       {a : A.centers → Finset Index} {h : ℝ} (hh : 0 < h)
--       (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
--         coverRegion (a i) h)
--       {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
--       {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
--       {φ : ∀ i, ((a i) × Fin 3) → Base → ℝ}
--       {K : ∀ i, ((a i) × Fin 3) → TopologicalSpace.Compacts Base}
--       {τ : ℝ} {s : ℝ≥0}
--       {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
--       {r : A.centers → ℝ} {ρ R : ℝ}
--       {reference : A.centers → SmallModes.Base → Tensor}
--       (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)) (hρ : 0 < ρ)
--       (Q : ∀ i, (a i) → PhaseBasis) (w : ∀ i, (a i) → Fin 3 → ℝ)
--       (hw : ∀ i k j, w i k j ≠ 0)
--       (hphase : ∀ i k j, coordinatePhase (φ i (k,j)) = phaseLinear (w i k j • (Q i k).ξ j))
--       (hcutoff : ∀ i k j x, x ∈ (c i (k,j)).e.source →
--         (d i (k,j)).cutoff ((c i (k,j)).e x) =
--           supportedCellCutoff (A.supportedPlaneWeight i) hh (hcover i) k.val x / w i k j)
--       (hform : ∀ i k j x, x ∈ (c i (k,j)).e.source →
--         (d i (k,j)).form ((c i (k,j)).e x) = (Q i k).Q j)
--       (hsupport : ∀ i k j, tsupport (supportedCellCutoff
--         (A.supportedPlaneWeight i) hh (hcover i) k.val) ⊆ (c i (k,j)).e.source)
--       (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
--         (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
--       (u : ∀ x : M, CovariantTwoTensor x)
--       (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--         (fun x => TotalSpace.mk' TensorFiber x (u x)))
--       (hsym : ∀ p v v', u p v v' = u p v' v)
--       (hball : ∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
--       {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
--       (f : ∀ x : M, CovariantTwoTensor x)
--       (hf : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--         (fun x => TotalSpace.mk' TensorFiber x (f x)))
--       {m : ℕ} {C : ℝ} (hτpos : 0 < τ) (hτs : τ ≤ s)
--       (hres : A.TensorWeightedBound s m C
--         (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u-f)) :
--
--       A.TensorWeightedBound τ m (δ^2*C) (A.finiteAtlasFreeMean d hρ δ q u-δ^2 • f)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.PhaseGrid.Index`, `OAI.ClosedSurfaceR4.PhaseGrid.coverRegion`, `OAI.ClosedSurfaceR4.PhaseGrid.gridCutoffCompact` and `OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff` (definitions bundle `OAIQ249SI000` of this split); `OAI.ClosedSurfaceR4.FiniteMean.InTrialBall`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.phaseLinear`, `OAI.ClosedSurfaceR4.PhaseGrid.Base`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePhase` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.chartCompact` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanFiberSpace` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasMean` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasFreeMean` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.chartedFamilyMean` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_adjusted_increment` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/GridFreeMeanIdentity.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_mean_residual)

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
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry
open PhaseGrid (Index coverRegion supportedCellCutoff)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanSectionNormed
local instance gridFreeMeanSectionSpace_r54d7e6_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance instDecidableEqSigmaSubtypeMemFinsetCentersProdIndexFinOfNatNat_1_r54d7e6_1 {a : A.centers → Finset Index} : DecidableEq (Σ i, ((a i) × Fin 3)) :=
  Classical.decEq _
theorem grid_free_mean_residual
    {a : A.centers → Finset Index} {h : ℝ} (hh : 0 < h)
    (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
      coverRegion (a i) h)
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ((a i) × Fin 3) → Base → ℝ}
    {K : ∀ i, ((a i) × Fin 3) → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : ∀ i, (a i) → PhaseBasis) (w : ∀ i, (a i) → Fin 3 → ℝ)
    (hw : ∀ i k j, w i k j ≠ 0)
    (hphase : ∀ i k j, coordinatePhase (φ i (k,j)) = phaseLinear (w i k j • (Q i k).ξ j))
    (hcutoff : ∀ i k j x, x ∈ (c i (k,j)).e.source →
      (d i (k,j)).cutoff ((c i (k,j)).e x) =
        supportedCellCutoff (A.supportedPlaneWeight i) hh (hcover i) k.val x / w i k j)
    (hform : ∀ i k j x, x ∈ (c i (k,j)).e.source →
      (d i (k,j)).form ((c i (k,j)).e x) = (Q i k).Q j)
    (hsupport : ∀ i k j, tsupport (supportedCellCutoff
      (A.supportedPlaneWeight i) hh (hcover i) k.val) ⊆ (c i (k,j)).e.source)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hsym : ∀ p v v', u p v v' = u p v' v)
    (hball : ∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (f : ∀ x : M, CovariantTwoTensor x)
    (hf : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (f x)))
    {m : ℕ} {C : ℝ} (hτpos : 0 < τ) (hτs : τ ≤ s)
    (hres : A.TensorWeightedBound s m C
      (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u-f)) :

    A.TensorWeightedBound τ m (δ^2*C) (A.finiteAtlasFreeMean d hρ δ q u-δ^2 • f) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
