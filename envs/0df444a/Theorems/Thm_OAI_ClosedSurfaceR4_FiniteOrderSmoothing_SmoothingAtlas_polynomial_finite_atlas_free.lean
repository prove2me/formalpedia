-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_finite_atlas_free
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_free
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:42:55.8387+00:00
-- url     : https://prove2.me/theorems/e1f5c550-e6d9-4b09-8a5b-c584ca2e0d55
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_free: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_free` of [lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialAtlasFree.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialAtlasFree.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean`):
--
--   ```lean
--   theorem polynomial_finite_atlas_free (q m : ℕ) :
--       ∃ (p : ℕ) (E Dv Dt : ℝ), 1 ≤ E ∧ 0 ≤ Dv ∧ 0 ≤ Dt ∧
--       ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)], ∀ n : ℕ,
--         (∀ i, Fintype.card (ι i) ≤ n) →
--       ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
--         {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
--         {τ : ℝ} {s : ℝ≥0}
--         {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
--           (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s}
--         {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
--         (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
--         ∀ C J : ℕ → ℝ,
--         (∀ i j, (c i j).C = C ∧ (c i j).J = J ∧ ∀ k, (c i j).D k = 0) →
--         ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
--         (∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
--           (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
--         ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
--         (∀ i j, (d i j).budgets.inv (m+q+1) ≤ B ∧ (d i j).budgets.forms (m+q+1) ≤ B ∧
--           (d i j).budgets.psi (m+q+1) ≤ B) →
--         ∀ N : ℕ → ℝ, (∀ k, 0 ≤ N k) →
--         (∀ i j, (d i j).budgets.normal (m+q+1) ≤ N (m+q+1)) →
--         ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ x : M, CovariantTwoTensor x,
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--           (fun x => TotalSpace.mk' TensorFiber x (u x)) →
--         (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
--         (∀ i, WeightedEstimates.WeightedBound univ s (m+q+1) B (A.tensorPlaneRead i u)) →
--         A.WeightedBound τ m
--           (Dv*(n : ℝ)*max 1 (metricFreeSizeBudget C J N q m)*(E*B^p)*(δ*τ))
--           (A.finiteAtlasFreeOscillation d hρ δ q u) ∧
--         A.TensorWeightedBound τ m
--           (Dt*(n : ℝ)*(τ/s)^(q+1)*max 1 (metricFreeResidualBudget C J N q m)*(E*B^p)*(δ*τ))
--           (linearMetricTensor F (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteMean.InTrialBall`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.metricFreeResidualBudget` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.metricFreeSizeBudget` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap_smooth` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearMetricTensor`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.emptyMetricPolynomial`, `OAI.ClosedSurfaceR4.PhaseMean.Budgets`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.chartCompact` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.realMap` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasFreeDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasFreeFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasFreeFiberSpace` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasFreeOscillation` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_forced_increment` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialAtlasFree.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_free)

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
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasFreeFiberSpace
local instance polynomialAtlasFreeDualAdd_rfed301_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasFreeDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasFreeFiberNormed
local instance polynomialAtlasFreeSectionNormed_rfed301_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialAtlasFreeSectionSpace_rfed301_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_finite_atlas_free (q m : ℕ) :
    ∃ (p : ℕ) (E Dv Dt : ℝ), 1 ≤ E ∧ 0 ≤ Dv ∧ 0 ≤ Dt ∧
    ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)], ∀ n : ℕ,
      (∀ i, Fintype.card (ι i) ≤ n) →
    ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
        (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s}
      {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
      (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      ∀ C J : ℕ → ℝ,
      (∀ i j, (c i j).C = C ∧ (c i j).J = J ∧ ∀ k, (c i j).D k = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      (∀ i j, (d i j).budgets.inv (m+q+1) ≤ B ∧ (d i j).budgets.forms (m+q+1) ≤ B ∧
        (d i j).budgets.psi (m+q+1) ≤ B) →
      ∀ N : ℕ → ℝ, (∀ k, 0 ≤ N k) →
      (∀ i j, (d i j).budgets.normal (m+q+1) ≤ N (m+q+1)) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i, WeightedEstimates.WeightedBound univ s (m+q+1) B (A.tensorPlaneRead i u)) →
      A.WeightedBound τ m
        (Dv*(n : ℝ)*max 1 (metricFreeSizeBudget C J N q m)*(E*B^p)*(δ*τ))
        (A.finiteAtlasFreeOscillation d hρ δ q u) ∧
      A.TensorWeightedBound τ m
        (Dt*(n : ℝ)*(τ/s)^(q+1)*max 1 (metricFreeResidualBudget C J N q m)*(E*B^p)*(δ*τ))
        (linearMetricTensor F (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u)) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
