-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_correctedPrimitiveAmplitude_smooth_of_data
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude_smooth_of_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:58.909192+00:00
-- url     : https://prove2.me/theorems/5c8c2336-4d44-4149-a1fe-0d575b7ef34e
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude_smooth_of_data (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude_smooth_of_data` of [lean/OAI/Geometry/SurfaceImmersion/Correction/TensorOperatorSmooth.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/TensorOperatorSmooth.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators`, `open PhaseMean PhaseGeometry`):
--
--   ```lean
--   theorem correctedPrimitiveAmplitude_smooth_of_data
--       (P : A.centers → JetPolynomial.Base → PhaseBasis)
--       (psi phi : (A.centers × Fin 3) → M → ℝ)
--       (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
--       (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
--       (hsupport : ∀ a, tsupport (psi a) ⊆ (chart (a.1 : M)).source)
--       (hQ : ∀ a p, p ∈ tsupport (psi a) →
--         ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
--       (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
--       (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
--       (u : ∀ p : M, CovariantTwoTensor p)
--       (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--         (fun p => TotalSpace.mk' TensorFiber p (u p)))
--       (hpos : ∀ a p, p ∈ tsupport (psi a) →
--         0 < A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p))
--       (a : A.centers × Fin 3) :
--       ContMDiff planeModel 𝓘(ℝ) ∞ (A.correctedPrimitiveAmplitude P psi phi u a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base` and `OAI.ClosedSurfaceR4.PhaseMean.Tensor` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothDualSmul` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualAdd` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberSpace` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoefficientField` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveTensor` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_smooth_family` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/TensorOperatorSmooth.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude_smooth_of_data)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberSpace
local instance operatorSmoothFiberComplete_rd52292_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberSpace
local instance operatorSmoothFiberComplete_rd52292_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothSectionNormed
local instance operatorSmoothSectionSpace_rd52292_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothSectionGroup
theorem correctedPrimitiveAmplitude_smooth_of_data
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi phi : (A.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hsupport : ∀ a, tsupport (psi a) ⊆ (chart (a.1 : M)).source)
    (hQ : ∀ a p, p ∈ tsupport (psi a) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 < A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p))
    (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.correctedPrimitiveAmplitude P psi phi u a) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
