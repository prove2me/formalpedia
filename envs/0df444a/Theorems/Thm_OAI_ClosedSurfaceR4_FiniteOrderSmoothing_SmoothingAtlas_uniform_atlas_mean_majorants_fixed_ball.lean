-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_atlas_mean_majorants_fixed_ball
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_atlas_mean_majorants_fixed_ball
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:45:00.521674+00:00
-- url     : https://prove2.me/theorems/2af11363-eade-43a0-94fc-be2b001658f9
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_atlas_mean_majorants_fixed_ball (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_atlas_mean_majorants_fixed_ball` of [lean/OAI/Geometry/SurfaceImmersion/Correction/UniformAtlasMean.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/UniformAtlasMean.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean`, `open JetPolynomial (Base)`, `open JetPolynomial.Perturbation`):
--
--   ```lean
--   theorem uniform_atlas_mean_majorants_fixed_ball
--       {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
--       (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
--       (reference : ∀ x : M, CovariantTwoTensor x)
--       (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--         (fun x => TotalSpace.mk' TensorFiber x (reference x))) (q : ℕ) :
--       let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
--       let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
--       ∀ r : ℝ, 0 ≤ r →
--         (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
--           InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
--           InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r)
--             (A.tensorPlaneRead i (A.tensorDecode f))) ∧ ∃ β κ : ℕ → ℝ → ℝ,
--         ∀ {ε τ : ℝ} {s : ℝ≥0}
--           (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i reference)),
--         (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
--         0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ loss ≤ 1 → ∀ δ : ℝ, 0 < δ →
--         MeanBounds univ s (A.tensorEncode reference) r L
--           (rescaledMean (τ / s + ε / τ ^ loss)
--             (A.tensorMeanOperator (A.atlasMean (fun i => (d i).mean hρ δ q)))) β κ
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteMean.InTrialBall`, `OAI.ClosedSurfaceR4.FiniteMean.MeanBounds`, `OAI.ClosedSurfaceR4.FiniteMean.rescaledMean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorLoss` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.SmallModes.Base` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorDecode` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformAtlasDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformAtlasFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformAtlasFiberSpace` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanProfile` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData.Fits` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasMean` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorMeanOperator` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorReadBallConstant` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData.mean` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorEncode` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.profiled_polynomial_atlas_small_increment` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/UniformAtlasMean.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_atlas_mean_majorants_fixed_ball)

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
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformAtlasFiberSpace
local instance uniformAtlasDualAdd_r8c5b73_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformAtlasFiberNormed
local instance uniformAtlasSectionNormed_r8c5b73_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformAtlasSectionSpace_r8c5b73_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem uniform_atlas_mean_majorants_fixed_ball
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x))) (q : ℕ) :
    let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∀ r : ℝ, 0 ≤ r →
      (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r)
          (A.tensorPlaneRead i (A.tensorDecode f))) ∧ ∃ β κ : ℕ → ℝ → ℝ,
      ∀ {ε τ : ℝ} {s : ℝ≥0}
        (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i reference)),
      (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ loss ≤ 1 → ∀ δ : ℝ, 0 < δ →
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean (τ / s + ε / τ ^ loss)
          (A.tensorMeanOperator (A.atlasMean (fun i => (d i).mean hρ δ q)))) β κ := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
