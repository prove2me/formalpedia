-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_charted_family_atlas_quadratic_residual
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.charted_family_atlas_quadratic_residual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:43:49.093045+00:00
-- url     : https://prove2.me/theorems/69b83c0d-f26f-445c-a540-5d51c072bab8
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.charted_family_atlas_quadratic_residual (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.charted_family_atlas_quadratic_residual` of [lean/OAI/Geometry/SurfaceImmersion/Correction/ChartedAtlasQuadraticResidual.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/ChartedAtlasQuadraticResidual.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open Set Manifold Bundle PhaseMean PhaseGeometry WeightedEstimates FiniteMean`, `open JetPolynomial (Base)`, `open JetPolynomial.Perturbation`):
--
--   ```lean
--   theorem charted_family_atlas_quadratic_residual
--       {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
--       {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
--       {reference : A.centers → SmallModes.Base → Tensor}
--       (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i)) (hρ : 0 < ρ)
--       (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
--       (hw : ∀ i j, w i j ≠ 0)
--       (hphase : ∀ i j, coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j))
--       (hcutoff : ∀ i j x, x ∈ ((d i).solver j).e.source →
--         ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j)
--       (hform : ∀ i j x, x ∈ ((d i).solver j).e.source →
--         ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j)
--       (hsupport : ∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source)
--       (u H : ∀ x : M, CovariantTwoTensor x)
--       (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--         (fun x => TotalSpace.mk' TensorFiber x (u x)))
--       (hH : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--         (fun x => TotalSpace.mk' TensorFiber x (H x)))
--       (hsym : ∀ x v v', u x v v' = u x v' v)
--       (hball : ∀ i, InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
--       {δ C : ℝ} {m : ℕ} (hδ : δ ≠ 0) (hτ : τ ≠ 0)
--       (q : ℕ)
--       (hb : A.TensorWeightedBound s m C
--         (u + A.atlasMean (fun i => (d i).mean hρ δ q) u - H)) :
--       A.TensorWeightedBound s m (δ^2*C)
--         (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteMean.InTrialBall`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField` and `OAI.ClosedSurfaceR4.PhaseMean.Tensor` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.phaseLinear`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.planeWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRestore`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePhase` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberSpace` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.chartCompact` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasMean` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData.mean` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData.quadraticMean` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_profiled_atlas_adjusted_mean` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.profiled_polynomial_atlas_small_increment` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/ChartedAtlasQuadraticResidual.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.charted_family_atlas_quadratic_residual)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
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
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasSectionNormed
local instance quadraticAtlasSectionSpace_r0df361_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem charted_family_atlas_quadratic_residual
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hphase : ∀ i j, coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j))
    (hcutoff : ∀ i j x, x ∈ ((d i).solver j).e.source →
      ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j)
    (hform : ∀ i j x, x ∈ ((d i).solver j).e.source →
      ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j)
    (hsupport : ∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source)
    (u H : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hH : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (H x)))
    (hsym : ∀ x v v', u x v v' = u x v' v)
    (hball : ∀ i, InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ C : ℝ} {m : ℕ} (hδ : δ ≠ 0) (hτ : τ ≠ 0)
    (q : ℕ)
    (hb : A.TensorWeightedBound s m C
      (u + A.atlasMean (fun i => (d i).mean hρ δ q) u - H)) :
    A.TensorWeightedBound s m (δ^2*C)
      (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
