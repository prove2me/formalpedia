-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_atlas_zeroPhase
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_zeroPhase
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:42:51.590503+00:00
-- url     : https://prove2.me/theorems/1d8ccab1-afe4-462b-8422-2c69f378d187
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_zeroPhase: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_zeroPhase` of [lean/OAI/Geometry/SurfaceImmersion/Correction/FiniteAtlasFreeMetric.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/FiniteAtlasFreeMetric.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean`):
--
--   ```lean
--   theorem finite_atlas_zeroPhase
--       (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
--       (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
--       (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
--         (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
--       A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 • RealModes.zeroPhaseSum τ
--         (fun a : Σ i, ι i => A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) a.1 a.2))
--         (fun a : Σ i, ι i => A.vectorPlaneRead k
--           (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)) x) =
--       A.tensorPlaneRestore (fun i => RealModes.zeroPhaseSum τ
--         (fun j => coordinatePhase (φ i j))
--         (fun j => coordinateAmplitude ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.SmallModes.Ambient`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.planeWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePhase` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinateAmplitude` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.RealModes.zeroPhaseSum`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteGlobalPhase` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteGlobalAmplitude` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData.freeAmplitude` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_free_metric` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/FiniteAtlasFreeMetric.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_zeroPhase)

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
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeFiberSpace
local instance finiteAtlasFreeDualSmul_rb91de4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeFiberNormed
local instance finiteAtlasFreeSectionNormed_rb91de4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance finiteAtlasFreeSectionSpace_rb91de4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasIndexDecidable
theorem finite_atlas_zeroPhase
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 • RealModes.zeroPhaseSum τ
      (fun a : Σ i, ι i => A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) a.1 a.2))
      (fun a : Σ i, ι i => A.vectorPlaneRead k
        (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)) x) =
    A.tensorPlaneRestore (fun i => RealModes.zeroPhaseSum τ
      (fun j => coordinatePhase (φ i j))
      (fun j => coordinateAmplitude ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)))) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
