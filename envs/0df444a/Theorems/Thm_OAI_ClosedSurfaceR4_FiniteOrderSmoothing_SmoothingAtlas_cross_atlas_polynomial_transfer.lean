-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_cross_atlas_polynomial_transfer
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:55:47.549192+00:00
-- url     : https://prove2.me/theorems/1ac70294-0311-4be8-950e-a342eb9bdd97
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_transfer: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_transfer` of [lean/OAI/Geometry/SurfaceImmersion/Correction/CrossAtlasPolynomialTransfer.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/CrossAtlasPolynomialTransfer.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators`, `open JetPolynomial (Base Expression planeCoordinateIsometry)`, `open JetPolynomial.Perturbation`):
--
--   ```lean
--   theorem cross_atlas_polynomial_transfer {n : B.centers → ℕ}
--       (P : ∀ j : B.centers, Fin 3 → Fin (n j) → Expression)
--       (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) :
--       ∃ Q : A.centers → Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
--         (∀ i k r, (Q i k r).SmoothCoeffs univ) ∧
--         ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F → ∀ ε : ℝ,
--           A.atlasPolynomialMetric Q ε F = B.atlasPolynomialMetric P ε F
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomialFamilyDegree` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialMetric` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_mean_approximation_in_atlas` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/CrossAtlasPolynomialTransfer.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_transfer)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression planeCoordinateIsometry)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance polyTransferFiberNormed_r1db849_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polyTransferFiberSpace_r1db849_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polyTransferDualAdd_r1db849_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polyTransferDualSmul_r1db849_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A B : SmoothingAtlas M)

local instance polyTransferSectionNormed_r1db849_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polyTransferSectionSpace_r1db849_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem cross_atlas_polynomial_transfer {n : B.centers → ℕ}
    (P : ∀ j : B.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) :
    ∃ Q : A.centers → Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ i k r, (Q i k r).SmoothCoeffs univ) ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F → ∀ ε : ℝ,
        A.atlasPolynomialMetric Q ε F = B.atlasPolynomialMetric P ε F := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
