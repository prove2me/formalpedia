-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_increment_bound
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_increment_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:32:02.074232+00:00
-- url     : https://prove2.me/theorems/963e8893-5f21-4a76-838b-7581ab3eea15
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_increment_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_increment_bound` of [lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialIncrementBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialIncrementBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle TopologicalSpace`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates`):
--
--   ```lean
--   theorem atlas_polynomial_increment_bound (m : ℕ) (A₀ B₀ : ℝ)
--       (hA : 0 ≤ A₀) (hB : 0 ≤ B₀) :
--       ∃ D : ℝ, 0 ≤ D ∧ ∀ {n : A.centers → ℕ}
--         (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
--         (_hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
--         (F U V : M → Space), ContMDiff planeModel spaceModel ∞ F →
--         ContMDiff planeModel spaceModel ∞ U → ContMDiff planeModel spaceModel ∞ V →
--         ∀ (T H : ∀ p : M, CovariantTwoTensor p),
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--           (fun p => TotalSpace.mk' TensorFiber p (T p)) →
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--           (fun p => TotalSpace.mk' TensorFiber p (H p)) →
--         ∀ (τ ε δ C₁ C₂ C₃ E₁ E₂ : ℝ), 0 < τ → τ ≤ 1 → 0 ≤ δ → δ ≤ τ →
--         A.WeightedBound τ (m+1) (A₀*(δ*τ)) U →
--         A.WeightedBound τ (m+1) (B₀*δ^2) V →
--         A.TensorWeightedBound τ m C₁
--           (linearMetricTensor F U+A.atlasPolynomialVariation P ε F U) →
--         A.TensorWeightedBound τ m C₂
--           (linearMetricTensor F V+A.atlasPolynomialVariation P ε F V+
--             (inducedTensor U+A.atlasPolynomialQuadratic P ε F U)-H) →
--         A.TensorWeightedBound τ m C₃ (H-T) →
--         A.TensorWeightedBound τ m (E₁*(δ^3/τ))
--           (A.atlasPolynomialQuadratic P ε F (U+V)-A.atlasPolynomialQuadratic P ε F U) →
--         A.TensorWeightedBound τ m (E₂*(δ^3/τ)) (A.atlasPolynomialRemainder P ε F (U+V)) →
--         A.TensorWeightedBound τ m (C₁+C₂+C₃+(D+E₁+E₂)*(δ^3/τ))
--           (A.atlasPolynomialMetric P ε (F+(U+V))-A.atlasPolynomialMetric P ε F-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialMetric` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearMetricTensor` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialIncrementDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialIncrementDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialIncrementFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialIncrementFiberSpace` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialQuadratic`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialRemainder` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialVariation` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_small_increment_fixed_phase` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialIncrementBound.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_increment_bound)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialIncrementDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialIncrementDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialIncrementFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialIncrementFiberSpace
local instance polynomialIncrementSectionNormed_rd55ef2_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialIncrementSectionSpace_rd55ef2_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem atlas_polynomial_increment_bound (m : ℕ) (A₀ B₀ : ℝ)
    (hA : 0 ≤ A₀) (hB : 0 ≤ B₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {n : A.centers → ℕ}
      (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
      (_hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
      (F U V : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ContMDiff planeModel spaceModel ∞ U → ContMDiff planeModel spaceModel ∞ V →
      ∀ (T H : ∀ p : M, CovariantTwoTensor p),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (T p)) →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (H p)) →
      ∀ (τ ε δ C₁ C₂ C₃ E₁ E₂ : ℝ), 0 < τ → τ ≤ 1 → 0 ≤ δ → δ ≤ τ →
      A.WeightedBound τ (m+1) (A₀*(δ*τ)) U →
      A.WeightedBound τ (m+1) (B₀*δ^2) V →
      A.TensorWeightedBound τ m C₁
        (linearMetricTensor F U+A.atlasPolynomialVariation P ε F U) →
      A.TensorWeightedBound τ m C₂
        (linearMetricTensor F V+A.atlasPolynomialVariation P ε F V+
          (inducedTensor U+A.atlasPolynomialQuadratic P ε F U)-H) →
      A.TensorWeightedBound τ m C₃ (H-T) →
      A.TensorWeightedBound τ m (E₁*(δ^3/τ))
        (A.atlasPolynomialQuadratic P ε F (U+V)-A.atlasPolynomialQuadratic P ε F U) →
      A.TensorWeightedBound τ m (E₂*(δ^3/τ)) (A.atlasPolynomialRemainder P ε F (U+V)) →
      A.TensorWeightedBound τ m (C₁+C₂+C₃+(D+E₁+E₂)*(δ^3/τ))
        (A.atlasPolynomialMetric P ε (F+(U+V))-A.atlasPolynomialMetric P ε F-T) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
