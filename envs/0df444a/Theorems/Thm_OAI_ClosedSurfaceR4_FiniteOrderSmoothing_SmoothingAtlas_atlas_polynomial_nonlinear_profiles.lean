-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_nonlinear_profiles
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_nonlinear_profiles
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:36:03.085942+00:00
-- url     : https://prove2.me/theorems/2fd92cdb-6def-4aff-a7b8-d0a448cc1967
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_nonlinear_profiles: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_nonlinear_profiles` of [lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialNonlinearProfiles.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialNonlinearProfiles.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology NNReal BigOperators Pointwise`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates`):
--
--   ```lean
--   theorem atlas_polynomial_nonlinear_profiles {n : A.centers → ℕ}
--       (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
--       (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
--       (Ω : A.centers → Set JetPolynomial.Base) (hΩ : ∀ i, IsOpen (Ω i))
--       (KΩ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩK : ∀ i, Ω i ⊆ KΩ i)
--       (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ω i)
--       (R U V : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) (hU : ∀ m, 0 ≤ U m) (hV : ∀ m, 0 ≤ V m) :
--       ∃ E₁ E₂ : ℕ → ℝ, (∀ m, 0 ≤ E₁ m) ∧ (∀ m, 0 ≤ E₂ m) ∧
--         ∀ (G X Y : M → Space), ContMDiff planeModel spaceModel ∞ G →
--         ContMDiff planeModel spaceModel ∞ X → ContMDiff planeModel spaceModel ∞ Y →
--         ∀ (s : ℝ≥0) (τ ε δ : ℝ), 0 < τ → 0 < (s:ℝ) → τ ≤ s → s ≤ 1 →
--         0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ τ →
--         (∀ i, ε/τ^tensorLoss (P i) ≤ 1) →
--         (∀ m, A.ShiftedBound 2 m s (R m) G) →
--         (∀ m, A.WeightedBound τ m (U m*(δ*τ)) X) →
--         (∀ m, A.WeightedBound τ m (V m*δ^2) Y) →
--         (∀ m, A.TensorWeightedBound τ m (E₁ m*(δ^3/τ))
--           (A.atlasPolynomialQuadratic P ε G (X+Y)-A.atlasPolynomialQuadratic P ε G X)) ∧
--         (∀ m, A.TensorWeightedBound τ m (E₂ m*(δ^3/τ))
--           (A.atlasPolynomialRemainder P ε G (X+Y)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorLoss` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.ShiftedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialQuadratic` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialRemainder` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_small_increment_fixed_phase` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialNonlinearProfiles.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_nonlinear_profiles)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
open Set Manifold Bundle
open scoped ContDiff Manifold Topology NNReal BigOperators Pointwise
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_polynomial_nonlinear_profiles {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (Ω : A.centers → Set JetPolynomial.Base) (hΩ : ∀ i, IsOpen (Ω i))
    (KΩ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩK : ∀ i, Ω i ⊆ KΩ i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ω i)
    (R U V : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) (hU : ∀ m, 0 ≤ U m) (hV : ∀ m, 0 ≤ V m) :
    ∃ E₁ E₂ : ℕ → ℝ, (∀ m, 0 ≤ E₁ m) ∧ (∀ m, 0 ≤ E₂ m) ∧
      ∀ (G X Y : M → Space), ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ X → ContMDiff planeModel spaceModel ∞ Y →
      ∀ (s : ℝ≥0) (τ ε δ : ℝ), 0 < τ → 0 < (s:ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ τ →
      (∀ i, ε/τ^tensorLoss (P i) ≤ 1) →
      (∀ m, A.ShiftedBound 2 m s (R m) G) →
      (∀ m, A.WeightedBound τ m (U m*(δ*τ)) X) →
      (∀ m, A.WeightedBound τ m (V m*δ^2) Y) →
      (∀ m, A.TensorWeightedBound τ m (E₁ m*(δ^3/τ))
        (A.atlasPolynomialQuadratic P ε G (X+Y)-A.atlasPolynomialQuadratic P ε G X)) ∧
      (∀ m, A.TensorWeightedBound τ m (E₂ m*(δ^3/τ))
        (A.atlasPolynomialRemainder P ε G (X+Y))) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
