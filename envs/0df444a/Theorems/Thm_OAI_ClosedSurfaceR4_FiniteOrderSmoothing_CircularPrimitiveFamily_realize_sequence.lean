-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_CircularPrimitiveFamily_realize_sequence
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.realize_sequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:07:02.88657+00:00
-- url     : https://prove2.me/theorems/4d16abeb-d89b-4518-b243-9a4ad556d9fa
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.realize_sequence: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.realize_sequence` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/CircularMetricSequence.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/CircularMetricSequence.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily`, with `open Set Manifold`, `open scoped ContDiff Topology`, `open SurfaceJetCoordinates SmallModes PhaseGeometry`):
--
--   ```lean
--    theorem realize_sequence (N : ℕ) :
--       ∀ (d : CircularPrimitiveFamily B (Fin N)) (g : Fin (N+1) → SmoothMetric M),
--       (∀ a : Fin N, (g a.succ).inner = (g a.castSucc).inner +
--         (fun p => (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p)) →
--       (∀ a : Fin N, d.ConvexMetric (g a.castSucc) a) →
--       ∀ (F : M → Space) (n : PreferredNormal F),
--       IsSmoothIsometricImmersion M (g 0) F → MetricGoodPhaseData (g 0) F →
--       FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n →
--       ∃ W : M → Space, IsSmoothIsometricImmersion M (g (Fin.last N)) W ∧
--         Nonempty (MetricGoodPhaseData (g (Fin.last N)) W) ∧ Nonempty (PreferredNormal W)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PreferredNormal` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryCrossingSet` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseDifferentialSquare` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.ConvexMetric` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.FiniteBoundaryGeometry` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.independent_circular_realization` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/CircularMetricSequence.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.realize_sequence)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace CircularPrimitiveFamily
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

 theorem realize_sequence (N : ℕ) :
    ∀ (d : CircularPrimitiveFamily B (Fin N)) (g : Fin (N+1) → SmoothMetric M),
    (∀ a : Fin N, (g a.succ).inner = (g a.castSucc).inner +
      (fun p => (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p)) →
    (∀ a : Fin N, d.ConvexMetric (g a.castSucc) a) →
    ∀ (F : M → Space) (n : PreferredNormal F),
    IsSmoothIsometricImmersion M (g 0) F → MetricGoodPhaseData (g 0) F →
    FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n →
    ∃ W : M → Space, IsSmoothIsometricImmersion M (g (Fin.last N)) W ∧
      Nonempty (MetricGoodPhaseData (g (Fin.last N)) W) ∧ Nonempty (PreferredNormal W) := by
  sorry

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
