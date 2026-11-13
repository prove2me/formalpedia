-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_cross_atlas_polynomial_representation
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_representation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:55:33.8483+00:00
-- url     : https://prove2.me/theorems/57773773-3e19-47bf-9af6-809373bf948a
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_representation: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_representation` of [lean/OAI/Geometry/SurfaceImmersion/Correction/CrossAtlasPolynomialRepresentation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/CrossAtlasPolynomialRepresentation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators`, `open JetPolynomial (Base Expression)`, `open JetPolynomial.Perturbation`):
--
--   ```lean
--   theorem cross_atlas_polynomial_representation {n : B.centers → ℕ}
--       (P : ∀ j : B.centers, Fin 3 → Fin (n j) → Expression)
--       (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) (i : A.centers) :
--       ∃ Q : Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
--         (∀ k r, (Q k r).SmoothCoeffs univ) ∧
--         ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
--           ∀ (x : Base), A.chartWeight i x ≠ 0 → ∀ ε : ℝ,
--             coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (JetPolynomial.planeCoordinateIsometry x) =
--               A.tensorChartRead i (B.atlasPolynomialValue P ε F) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeight` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomialFamilyDegree` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialValue` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorChartRead` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePolynomialValue` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_transfer` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/CrossAtlasPolynomialRepresentation.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_representation)

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
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance crossPolyRepFiberNormed_r901aa3_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance crossPolyRepFiberSpace_r901aa3_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance crossPolyRepDualAdd_r901aa3_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance crossPolyRepDualSmul_r901aa3_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A B : SmoothingAtlas M)

local instance crossPolyRepSectionNormed_r901aa3_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossPolyRepSectionSpace_r901aa3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem cross_atlas_polynomial_representation {n : B.centers → ℕ}
    (P : ∀ j : B.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) (i : A.centers) :
    ∃ Q : Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ k r, (Q k r).SmoothCoeffs univ) ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ∀ (x : Base), A.chartWeight i x ≠ 0 → ∀ ε : ℝ,
          coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (JetPolynomial.planeCoordinateIsometry x) =
            A.tensorChartRead i (B.atlasPolynomialValue P ε F) x := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
