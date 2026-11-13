-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_finite_atlas_mean
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:42:46.735368+00:00
-- url     : https://prove2.me/theorems/5ae635ef-d977-41f3-bf57-d79321cf83de
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_mean: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_mean` of [lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialFiniteAtlasMean.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialFiniteAtlasMean.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates FiniteMean`):
--
--   ```lean
--   theorem polynomial_finite_atlas_mean (q : ℕ) :
--       ∃ (p : ℕ → ℕ) (C D E : ℕ → ℝ),
--         (∀ m, 1 ≤ C m) ∧ (∀ m, 1 ≤ D m) ∧ (∀ m, 0 ≤ E m) ∧
--       ∀ (reference : ∀ x : M, CovariantTwoTensor x),
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--           (fun x => TotalSpace.mk' TensorFiber x (reference x)) →
--       ∀ r : ℝ, 0 ≤ r → ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
--         {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
--         {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
--         {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
--         {τ : ℝ} {s : ℝ≥0}
--         {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
--         {ρ R : ℝ}
--         (d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i reference)),
--         ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
--         ∀ H B : ℕ → ℝ, (∀ m, 1 ≤ H m) → (∀ m, 0 ≤ B m) →
--         (∀ i m, (Fintype.card (ι i) : ℝ) ≤ H m ∧ ρ⁻¹ ≤ H m) →
--         (∀ i j m, (d i j).budgets.inv m ≤ B m ∧ (d i j).budgets.chi m ≤ B m ∧
--           (d i j).budgets.forms m ≤ B m ∧ (d i j).budgets.pull m ≤ B m ∧
--           (d i j).budgets.psi m ≤ B m ∧ (d i j).budgets.normal m ≤ B m ∧
--           (d i j).budgets.mode m ≤ B m) →
--         ∀ δ : ℝ, 0 < δ → MeanBounds univ s (A.tensorEncode reference) r (q+2)
--           (rescaledMean (τ/s) (A.tensorMeanOperator
--             (A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q))))
--           (polynomialMeanProfile (fun m => 2*p m+2) (fun m => 1+C m)
--             (transportedMeanGeometry (q+2) (meanGeometryEnvelope q H B) D E))
--           (polynomialMeanProfile (fun m => 2*p m+2) (fun m => 1+C m)
--             (transportedMeanGeometry (q+2) (meanGeometryEnvelope q H B) D E))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteMean.MeanBounds`, `OAI.ClosedSurfaceR4.FiniteMean.rescaledMean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.Space` and `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PhaseMean.polynomialMeanProfile`, `OAI.ClosedSurfaceR4.PhaseMean.transportedMeanGeometry` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.meanGeometryEnvelope` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.SmallModes.Base` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteMeanDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteMeanFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteMeanFiberSpace` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData`, `OAI.ClosedSurfaceR4.PhaseMean.Budgets`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.chartCompact` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.realMap` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasMean` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorMeanOperator` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorReadBallConstant` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.chartedFamilyMean` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorEncode` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_adjusted_increment` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_trial` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialFiniteAtlasMean.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_mean)

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
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates FiniteMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteMeanFiberSpace
local instance polynomialFiniteMeanDualAdd_r2a6452_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteMeanFiberNormed
local instance polynomialFiniteMeanSectionNormed_r2a6452_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialFiniteMeanSectionSpace_r2a6452_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_finite_atlas_mean (q : ℕ) :
    ∃ (p : ℕ → ℕ) (C D E : ℕ → ℝ),
      (∀ m, 1 ≤ C m) ∧ (∀ m, 1 ≤ D m) ∧ (∀ m, 0 ≤ E m) ∧
    ∀ (reference : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (reference x)) →
    ∀ r : ℝ, 0 ≤ r → ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
      {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
      {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
      {ρ R : ℝ}
      (d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i reference)),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ H B : ℕ → ℝ, (∀ m, 1 ≤ H m) → (∀ m, 0 ≤ B m) →
      (∀ i m, (Fintype.card (ι i) : ℝ) ≤ H m ∧ ρ⁻¹ ≤ H m) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m ∧ (d i j).budgets.chi m ≤ B m ∧
        (d i j).budgets.forms m ≤ B m ∧ (d i j).budgets.pull m ≤ B m ∧
        (d i j).budgets.psi m ≤ B m ∧ (d i j).budgets.normal m ≤ B m ∧
        (d i j).budgets.mode m ≤ B m) →
      ∀ δ : ℝ, 0 < δ → MeanBounds univ s (A.tensorEncode reference) r (q+2)
        (rescaledMean (τ/s) (A.tensorMeanOperator
          (A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q))))
        (polynomialMeanProfile (fun m => 2*p m+2) (fun m => 1+C m)
          (transportedMeanGeometry (q+2) (meanGeometryEnvelope q H B) D E))
        (polynomialMeanProfile (fun m => 2*p m+2) (fun m => 1+C m)
          (transportedMeanGeometry (q+2) (meanGeometryEnvelope q H B) D E)) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
