-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_atlas_increment_bound
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_increment_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:39:42.452852+00:00
-- url     : https://prove2.me/theorems/8a434432-31d0-49a6-a11e-19c90a4fab9c
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_increment_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_increment_bound` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/FiniteAtlasIncrement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/FiniteAtlasIncrement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean`):
--
--   ```lean
--   theorem finite_atlas_increment_bound (m : ℕ) :
--       ∃ D : ℝ, 0 ≤ D ∧ ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
--         {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
--         {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
--         {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
--         {τ : ℝ} {s : ℝ≥0}
--         {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
--         {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
--         (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
--         (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
--         (_hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
--           (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
--         (F V : M → Space), ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ V →
--         ∀ H : ∀ x : M, CovariantTwoTensor x,
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--           (fun x => TotalSpace.mk' TensorFiber x (H x)) →
--         0 < τ → τ ≤ 1 → 0 < δ → δ ≤ τ → ∀ A₀ B₀ C₁ C₂ C₃ : ℝ,
--         0 ≤ A₀ → 0 ≤ B₀ →
--         let U := spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u
--         A.WeightedBound τ (m+1) (A₀*(δ*τ)) U →
--         A.WeightedBound τ (m+1) (B₀*δ^2) V →
--         A.TensorWeightedBound τ m C₁ (linearMetricTensor F U) →
--         A.TensorWeightedBound τ m C₂ (linearMetricTensor F V + A.finiteAtlasNonzero d hρ δ q u) →
--         A.TensorWeightedBound τ m C₃ (A.finiteAtlasFreeMean d hρ δ q u - δ^2 • H) →
--         A.TensorWeightedBound τ m (C₁+C₂+C₃+D*(2*A₀*B₀+B₀^2)*(δ^3/τ))
--           (inducedTensor (F+(U+V)) - inducedTensor F - δ^2 • H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearMetricTensor` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementFiberSpace` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasFreeMean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasFreeOscillation` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasNonzero` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_forced_increment` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/FiniteAtlasIncrement.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_increment_bound)

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
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementSectionNormed
local instance finiteIncrementSectionSpace_rba1480_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem finite_atlas_increment_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
      {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
      {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
      {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
      (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
      (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
      (_hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
      (F V : M → Space), ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ V →
      ∀ H : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      0 < τ → τ ≤ 1 → 0 < δ → δ ≤ τ → ∀ A₀ B₀ C₁ C₂ C₃ : ℝ,
      0 ≤ A₀ → 0 ≤ B₀ →
      let U := spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u
      A.WeightedBound τ (m+1) (A₀*(δ*τ)) U →
      A.WeightedBound τ (m+1) (B₀*δ^2) V →
      A.TensorWeightedBound τ m C₁ (linearMetricTensor F U) →
      A.TensorWeightedBound τ m C₂ (linearMetricTensor F V + A.finiteAtlasNonzero d hρ δ q u) →
      A.TensorWeightedBound τ m C₃ (A.finiteAtlasFreeMean d hρ δ q u - δ^2 • H) →
      A.TensorWeightedBound τ m (C₁+C₂+C₃+D*(2*A₀*B₀+B₀^2)*(δ^3/τ))
        (inducedTensor (F+(U+V)) - inducedTensor F - δ^2 • H) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
