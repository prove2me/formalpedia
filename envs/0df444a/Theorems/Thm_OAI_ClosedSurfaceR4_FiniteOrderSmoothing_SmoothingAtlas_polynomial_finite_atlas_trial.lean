-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_finite_atlas_trial
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_trial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:43:51.169934+00:00
-- url     : https://prove2.me/theorems/8910711f-72e7-474c-ae6f-a39526ce0125
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_trial: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_trial` of [lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialFiniteAtlasTrial.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialFiniteAtlasTrial.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes`):
--
--   ```lean
--   theorem polynomial_finite_atlas_trial (q : ℕ) (B H Y : ℕ → ℝ → ℝ)
--       (hB : ∀ m, HasPolynomialBound (B m)) (hH : ∀ m, HasPolynomialBound (H m))
--       (hY : ∀ m, HasPolynomialBound (Y m)) :
--       ∃ e : ℕ, ∃ E : ℝ, ∃ S T : ℕ → ℝ → ℝ, 1 ≤ E ∧
--         (∀ m, HasPolynomialBound (S m)) ∧ (∀ m, HasPolynomialBound (T m)) ∧
--       ∀ x : ℝ, 1 ≤ x →
--       ∀ (reference : ∀ y : M, CovariantTwoTensor y),
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--           (fun y => TotalSpace.mk' TensorFiber y (reference y)) →
--       ∀ r : ℝ, 0 < r → ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
--         {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
--         {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
--         {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
--         {τ : ℝ} {s : ℝ≥0}
--         {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
--         {ρ R : ℝ}
--         (d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R
--           (A.tensorPlaneRead i reference)),
--         ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
--         (∀ m, 1 ≤ H m x) → (∀ m, 1 ≤ Y m x) →
--         (∀ i m, (Fintype.card (ι i) : ℝ) ≤ H m x ∧ ρ⁻¹ ≤ H m x) →
--         (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.chi m ≤ B m x ∧
--           (d i j).budgets.forms m ≤ B m x ∧ (d i j).budgets.pull m ≤ B m x ∧
--           (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ B m x ∧
--           (d i j).budgets.mode m ≤ B m x) →
--         (τ/s) ≤ min 1 ((r-r/2)/(2*(E*x^e))) →
--         ∀ f : ∀ y : M, CovariantTwoTensor y,
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--           (fun y => TotalSpace.mk' TensorFiber y (f y)) →
--         (∀ y v w, f y v w = f y w v) →
--         (∀ y, ‖A.tensorEncode f y-A.tensorEncode reference y‖ ≤ r/2) →
--         (∀ m, A.TensorWeightedBound s m (Y m x) f) →
--         ∀ δ : ℝ, 0 < δ → ∃ u : ∀ y : M, CovariantTwoTensor y,
--           ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--             (fun y => TotalSpace.mk' TensorFiber y (u y)) ∧
--           (∀ y v w, u y v w = u y w v) ∧
--           FiniteMean.InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode u) ∧
--           (∀ i, FiniteMean.InTrialBall univ (A.tensorPlaneRead i reference)
--             (A.tensorReadBallConstant*r) (A.tensorPlaneRead i u)) ∧
--           (∀ m, A.TensorWeightedBound s m (S m x) u) ∧
--           (∀ m, A.TensorWeightedBound s m (T m x*(τ/s)^(q+1))
--             (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u-f))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteMean.InTrialBall`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField` and `OAI.ClosedSurfaceR4.PhaseMean.Tensor` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.HasPolynomialBound` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.SmallModes.Base` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteTrialDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteTrialDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteTrialFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteTrialFiberSpace` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData`, `OAI.ClosedSurfaceR4.PhaseMean.Budgets`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.chartCompact` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.realMap` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasMean` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorReadBallConstant` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.chartedFamilyMean` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorEncode` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_geometric_increment` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialFiniteAtlasTrial.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_trial)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
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
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteTrialDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteTrialDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteTrialFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteTrialFiberSpace
local instance polynomialFiniteTrialSectionNormed_re2574e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialFiniteTrialSectionSpace_re2574e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_finite_atlas_trial (q : ℕ) (B H Y : ℕ → ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) (hH : ∀ m, HasPolynomialBound (H m))
    (hY : ∀ m, HasPolynomialBound (Y m)) :
    ∃ e : ℕ, ∃ E : ℝ, ∃ S T : ℕ → ℝ → ℝ, 1 ≤ E ∧
      (∀ m, HasPolynomialBound (S m)) ∧ (∀ m, HasPolynomialBound (T m)) ∧
    ∀ x : ℝ, 1 ≤ x →
    ∀ (reference : ∀ y : M, CovariantTwoTensor y),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (reference y)) →
    ∀ r : ℝ, 0 < r → ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
      {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
      {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
      {ρ R : ℝ}
      (d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R
        (A.tensorPlaneRead i reference)),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, 1 ≤ H m x) → (∀ m, 1 ≤ Y m x) →
      (∀ i m, (Fintype.card (ι i) : ℝ) ≤ H m x ∧ ρ⁻¹ ≤ H m x) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.chi m ≤ B m x ∧
        (d i j).budgets.forms m ≤ B m x ∧ (d i j).budgets.pull m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ B m x ∧
        (d i j).budgets.mode m ≤ B m x) →
      (τ/s) ≤ min 1 ((r-r/2)/(2*(E*x^e))) →
      ∀ f : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (f y)) →
      (∀ y v w, f y v w = f y w v) →
      (∀ y, ‖A.tensorEncode f y-A.tensorEncode reference y‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (Y m x) f) →
      ∀ δ : ℝ, 0 < δ → ∃ u : ∀ y : M, CovariantTwoTensor y,
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
          (fun y => TotalSpace.mk' TensorFiber y (u y)) ∧
        (∀ y v w, u y v w = u y w v) ∧
        FiniteMean.InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode u) ∧
        (∀ i, FiniteMean.InTrialBall univ (A.tensorPlaneRead i reference)
          (A.tensorReadBallConstant*r) (A.tensorPlaneRead i u)) ∧
        (∀ m, A.TensorWeightedBound s m (S m x) u) ∧
        (∀ m, A.TensorWeightedBound s m (T m x*(τ/s)^(q+1))
          (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u-f)) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
