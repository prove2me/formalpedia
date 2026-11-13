-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_reference_circular_starting_family
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_circular_starting_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:27.040547+00:00
-- url     : https://prove2.me/theorems/bce5f79e-2433-4efe-b470-9a5ae28c00b5
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_circular_starting_family: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_circular_starting_family` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/ReferenceBoundaryStartingFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/ReferenceBoundaryStartingFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold`, `open scoped ContDiff Topology`, `open SmallModes RealModes VelocityFrame`):
--
--   ```lean
--   theorem reference_circular_starting_family (g : SmoothMetric M) {I : M → Space}
--       (hI : ContMDiff planeModel spaceModel ∞ I) (hunit : ∀ p, ‖I p‖ = 1)
--       (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel I p))
--       {η : ℝ} (hη : 0 < η) :
--       ∃ r D c : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ D ∧ 0 < c ∧
--         A.WeightedBound 1 2 D I ∧
--         A.TensorWeightedBound 1 1 η (inducedTensor (r • I)) ∧
--         (∀ p v, inducedForm (r • I) p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
--         ∀ (n : ℕ) (B : SmoothingAtlas M) (d : CircularFamilyGeometry B (Fin n))
--           (ε : ℝ), 0 < ε →
--         ∃ (G : M → Space) (g₀ : SmoothMetric M) (normal : PreferredNormal (r • G)),
--           ContMDiff planeModel spaceModel ∞ G ∧ (∀ p, ‖G p‖ = 1) ∧
--           IsSmoothIsometricImmersion M g₀ (r • G) ∧
--           g₀.inner = inducedTensor (r • G) ∧ Nonempty (MetricGoodPhaseData g₀ (r • G)) ∧
--           normal.vector = (fun p => -G p) ∧
--           A.WeightedBound 1 1 ε (G-I) ∧ A.WeightedBound 1 2 D G ∧
--           (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) ∧
--           A.TensorWeightedBound 1 1 η g₀.inner ∧
--           (∀ p v, g₀.inner p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
--           FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) (r • G) normal
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.inducedForm` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PreferredNormal` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryCrossingSet` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularFamilyGeometry` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.FiniteBoundaryGeometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.isometric_immersion_of_spherical_immersion` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/ReferenceBoundaryStartingFamily.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_circular_starting_family)

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

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem reference_circular_starting_family (g : SmoothMetric M) {I : M → Space}
    (hI : ContMDiff planeModel spaceModel ∞ I) (hunit : ∀ p, ‖I p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel I p))
    {η : ℝ} (hη : 0 < η) :
    ∃ r D c : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ D ∧ 0 < c ∧
      A.WeightedBound 1 2 D I ∧
      A.TensorWeightedBound 1 1 η (inducedTensor (r • I)) ∧
      (∀ p v, inducedForm (r • I) p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
      ∀ (n : ℕ) (B : SmoothingAtlas M) (d : CircularFamilyGeometry B (Fin n))
        (ε : ℝ), 0 < ε →
      ∃ (G : M → Space) (g₀ : SmoothMetric M) (normal : PreferredNormal (r • G)),
        ContMDiff planeModel spaceModel ∞ G ∧ (∀ p, ‖G p‖ = 1) ∧
        IsSmoothIsometricImmersion M g₀ (r • G) ∧
        g₀.inner = inducedTensor (r • G) ∧ Nonempty (MetricGoodPhaseData g₀ (r • G)) ∧
        normal.vector = (fun p => -G p) ∧
        A.WeightedBound 1 1 ε (G-I) ∧ A.WeightedBound 1 2 D G ∧
        (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) ∧
        A.TensorWeightedBound 1 1 η g₀.inner ∧
        (∀ p v, g₀.inner p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
        FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) (r • G) normal := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
