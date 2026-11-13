-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_remainder_bound
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_remainder_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:56.593665+00:00
-- url     : https://prove2.me/theorems/0ace69b2-436a-4562-b9a4-61a7299396f8
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_remainder_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_remainder_bound` of [lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialRemainderBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialRemainderBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle TopologicalSpace`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates`):
--
--   ```lean
--   theorem atlas_polynomial_remainder_bound {n : A.centers → ℕ}
--       (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
--       (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
--       (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
--       (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
--       (Q : A.centers → Set LowJet) (hQ : ∀ i, IsCompact (Q i))
--       (m : ℕ) (B C : A.centers → ℝ) (hB : ∀ i, 1 ≤ B i) (hC : ∀ i, 0 < C i) :
--       ∃ E : ℝ, 0 ≤ E ∧ ∀ (F X : M → Space),
--         ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ X →
--         ∀ τ ε δ : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ →
--         (∀ i, ε/τ^tensorLoss (P i) ≤ 1) →
--         (∀ i t, t ∈ Icc (0 : ℝ) 1 → MapsTo
--           (lowJet (fun x => A.jetChartMap i F x+t • A.jetChartMap i X x)) (U i) (Q i)) →
--         (∀ i t, t ∈ Icc (0 : ℝ) 1 → WeightedEstimates.WeightedBound (U i) τ
--           (m+tensorOrder (P i)) (B i)
--           (lowJet (fun x => A.jetChartMap i F x+t • A.jetChartMap i X x))) →
--         (∀ i, WeightedEstimates.WeightedBound univ τ (m+tensorOrder (P i))
--           (C i*δ*τ) (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)) →
--         A.TensorWeightedBound τ m (E*(δ^3/τ)) (A.atlasPolynomialRemainder P ε F X)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorLoss` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialRemainder` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_nonlinear_profiles` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialRemainderBounds.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_remainder_bound)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
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
local instance atlasRemainderFiberNormed_r1d73c4_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasRemainderFiberSpace_r1d73c4_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasRemainderDualAdd_r1d73c4_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasRemainderDualSmul_r1d73c4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasRemainderSectionNormed_r1d73c4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasRemainderSectionSpace_r1d73c4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem atlas_polynomial_remainder_bound {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
    (Q : A.centers → Set LowJet) (hQ : ∀ i, IsCompact (Q i))
    (m : ℕ) (B C : A.centers → ℝ) (hB : ∀ i, 1 ≤ B i) (hC : ∀ i, 0 < C i) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (F X : M → Space),
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ X →
      ∀ τ ε δ : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ →
      (∀ i, ε/τ^tensorLoss (P i) ≤ 1) →
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → MapsTo
        (lowJet (fun x => A.jetChartMap i F x+t • A.jetChartMap i X x)) (U i) (Q i)) →
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → WeightedEstimates.WeightedBound (U i) τ
        (m+tensorOrder (P i)) (B i)
        (lowJet (fun x => A.jetChartMap i F x+t • A.jetChartMap i X x))) →
      (∀ i, WeightedEstimates.WeightedBound univ τ (m+tensorOrder (P i))
        (C i*δ*τ) (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)) →
      A.TensorWeightedBound τ m (E*(δ^3/τ)) (A.atlasPolynomialRemainder P ε F X) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
