-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_corrected_smooth_family
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_smooth_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:11:20.484232+00:00
-- url     : https://prove2.me/theorems/1d6c897b-9a93-4027-a02a-4f5d1773da81
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_smooth_family: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_smooth_family` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/ReferenceCorrectedFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/ReferenceCorrectedFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem corrected_smooth_family {F : M → Space}
--       (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
--       (href : gref.inner = g.inner-inducedTensor (r • F)) :
--       ∃ phaseTol weightTol mapTol : ℝ, 0 < phaseTol ∧ 0 < weightTol ∧ 0 < mapTol ∧
--         ∀ (ell : d.B.centers → Fin 3 → SmallModes.Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
--         (∀ i j, ‖ell i j-(d.P i).ξ j‖ < phaseTol) →
--         (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a)) →
--         (∀ a p, 0 ≤ psi a p) →
--         (∀ a, tsupport (psi a) ⊆ tsupport (d.B.weight a.1)) →
--         (∀ a p, |psi a p-d.B.weight a.1 p| < weightTol) →
--         ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
--         A.WeightedBound 1 1 mapTol (G-F) →
--         ∃ f : SmoothPrimitiveFamily (d.B.centers × Fin 3) (g.inner-inducedTensor (r • G)),
--           f.phase = d.perturbedPhases ell ∧
--           f.amplitude = d.B.correctedPrimitiveAmplitude d.basis psi (d.perturbedPhases ell)
--             (g.inner-inducedTensor (r • G)) ∧
--           (∀ a p, 0 ≤ f.amplitude a p) ∧
--           (∀ a p, 0 < f.amplitude a p ↔ 0 < psi a p) ∧
--           ∀ a, tsupport (f.amplitude a) ⊆ tsupport (psi a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor` and `OAI.ClosedSurfaceR4.SmallModes.Base` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.basis` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.perturbedPhases` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas` and `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_cycles` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/ReferenceCorrectedFamily.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_smooth_family)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
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
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
local instance referenceFamilyFiberNormed_r051ed7_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance referenceFamilyFiberSpace_r051ed7_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance referenceFamilyDualAdd_r051ed7_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance referenceFamilyDualSmul_r051ed7_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

local instance referenceFamilySectionNormed_r051ed7_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance referenceFamilySectionSpace_r051ed7_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem corrected_smooth_family {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F)) :
    ∃ phaseTol weightTol mapTol : ℝ, 0 < phaseTol ∧ 0 < weightTol ∧ 0 < mapTol ∧
      ∀ (ell : d.B.centers → Fin 3 → SmallModes.Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ < phaseTol) →
      (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a)) →
      (∀ a p, 0 ≤ psi a p) →
      (∀ a, tsupport (psi a) ⊆ tsupport (d.B.weight a.1)) →
      (∀ a p, |psi a p-d.B.weight a.1 p| < weightTol) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 mapTol (G-F) →
      ∃ f : SmoothPrimitiveFamily (d.B.centers × Fin 3) (g.inner-inducedTensor (r • G)),
        f.phase = d.perturbedPhases ell ∧
        f.amplitude = d.B.correctedPrimitiveAmplitude d.basis psi (d.perturbedPhases ell)
          (g.inner-inducedTensor (r • G)) ∧
        (∀ a p, 0 ≤ f.amplitude a p) ∧
        (∀ a p, 0 < f.amplitude a p ↔ 0 < psi a p) ∧
        ∀ a, tsupport (f.amplitude a) ⊆ tsupport (psi a) := by
  sorry

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
