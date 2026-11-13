-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_tensorSmooth_symmetric
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth_symmetric
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:36.031308+00:00
-- url     : https://prove2.me/theorems/f14dab92-3192-4374-a4cd-dc3ca6fa40f0
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth_symmetric: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth_symmetric` of [lean/OAI/Geometry/SurfaceImmersion/Correction/TensorSmoothingSymmetry.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/TensorSmoothingSymmetry.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open scoped ContDiff Manifold Topology`, `open Set Manifold Bundle`, `open JetPolynomial (Base)`):
--
--   ```lean
--   theorem tensorSmooth_symmetric (r : ℕ) {s : ℝ} (hs : 0 < s)
--       {u : ∀ p : M, CovariantTwoTensor p}
--       (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--         (fun p => TotalSpace.mk' TensorFiber p (u p)))
--       (hsymm : ∀ p v w, u p v w = u p w v) :
--       ∀ p v w, A.tensorSmooth r s u p v w = A.tensorSmooth r s u p w v
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryDualSmul` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_smoothed_increment` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/TensorSmoothingSymmetry.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth_symmetric)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_r282638_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_r282638_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

theorem tensorSmooth_symmetric (r : ℕ) {s : ℝ} (hs : 0 < s)
    {u : ∀ p : M, CovariantTwoTensor p}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hsymm : ∀ p v w, u p v w = u p w v) :
    ∀ p v w, A.tensorSmooth r s u p v w = A.tensorSmooth r s u p w v := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
