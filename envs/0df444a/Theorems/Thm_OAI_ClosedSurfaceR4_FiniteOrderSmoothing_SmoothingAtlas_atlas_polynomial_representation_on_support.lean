-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_representation_on_support
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_representation_on_support
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:51:59.035908+00:00
-- url     : https://prove2.me/theorems/7969c6be-31fd-4491-b5bf-895cb98c466a
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_representation_on_support (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_representation_on_support` of [lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialLocalModel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialLocalModel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean`):
--
--   ```lean
--   theorem atlas_polynomial_representation_on_support {n : A.centers → ℕ}
--       (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
--       (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) (i : A.centers) :
--       ∃ Q : Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
--         (∀ k r, (Q k r).SmoothCoeffs univ) ∧
--         ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
--           ∀ x ∈ (A.chartWeightCompact i : Set Base), ∀ ε : ℝ,
--             coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (planeCoordinateIsometry x) =
--               A.tensorChartRead i (A.atlasPolynomialValue P ε F) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomialFamilyDegree` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialValue` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorChartRead` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePolynomialValue` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.full_linearized_representatives` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialLocalModel.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_representation_on_support)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
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
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance localModelFiberNormed_r598e80_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance localModelFiberSpace_r598e80_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance localModelDualAdd_r598e80_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance localModelDualSmul_r598e80_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance localModelSectionNormed_r598e80_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance localModelSectionSpace_r598e80_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem atlas_polynomial_representation_on_support {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) (i : A.centers) :
    ∃ Q : Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ k r, (Q k r).SmoothCoeffs univ) ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ∀ x ∈ (A.chartWeightCompact i : Set Base), ∀ ε : ℝ,
          coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (planeCoordinateIsometry x) =
            A.tensorChartRead i (A.atlasPolynomialValue P ε F) x := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
