-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitive_term_background_C1_bound
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_term_background_C1_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:06:16.203478+00:00
-- url     : https://prove2.me/theorems/08e09014-6c21-4449-ad2d-9cefaeec4b19
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_term_background_C1_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_term_background_C1_bound` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/PrimitiveTermC1Bounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/PrimitiveTermC1Bounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Filter Manifold Bundle`, `open scoped ContDiff Topology BigOperators`, `open WeightedEstimates`):
--
--   ```lean
--   theorem primitive_term_background_C1_bound (A : SmoothingAtlas M) {D : ℝ} (hD : 0 ≤ D) :
--       ∃ E : ℝ, 0 ≤ E ∧ ∀ amp phi : M → ℝ,
--         ContMDiff planeModel 𝓘(ℝ) ∞ amp → ContMDiff planeModel 𝓘(ℝ) ∞ phi →
--         (∀ i p, p ∈ tsupport (B.weight i) →
--           |amp p| ≤ D ∧ ‖fderiv ℝ (amp ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ D) →
--         (∀ i y, y ∈ (B.chartWeightCompact i : Set JetPolynomial.Base) →
--           ‖B.phaseCovectorRead i phi y‖ ≤ D ∧
--             ‖fderiv ℝ (B.phaseCovectorRead i phi) y‖ ≤ D) →
--         A.TensorWeightedBound 1 1 E (fun p => (amp p)^2 • phaseDifferentialSquare phi p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseDifferentialSquare` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseCovectorRead` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.termBoundDualSpace` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_corrected_term_C1` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/PrimitiveTermC1Bounds.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_term_background_C1_bound)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI006
import Definitions.Def_OAIQ249SI007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.termBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.termBoundFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.termBoundDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.termBoundDualSpace
local instance termBoundDualSmul_rcc46a2_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.termBoundSectionNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.termBoundFiberNormed
local instance termBoundSectionSpace_rcc46a2_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem primitive_term_background_C1_bound (A : SmoothingAtlas M) {D : ℝ} (hD : 0 ≤ D) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ amp phi : M → ℝ,
      ContMDiff planeModel 𝓘(ℝ) ∞ amp → ContMDiff planeModel 𝓘(ℝ) ∞ phi →
      (∀ i p, p ∈ tsupport (B.weight i) →
        |amp p| ≤ D ∧ ‖fderiv ℝ (amp ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ D) →
      (∀ i y, y ∈ (B.chartWeightCompact i : Set JetPolynomial.Base) →
        ‖B.phaseCovectorRead i phi y‖ ≤ D ∧
          ‖fderiv ℝ (B.phaseCovectorRead i phi) y‖ ≤ D) →
      A.TensorWeightedBound 1 1 E (fun p => (amp p)^2 • phaseDifferentialSquare phi p) := by
  sorry

end SmoothingAtlas

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
