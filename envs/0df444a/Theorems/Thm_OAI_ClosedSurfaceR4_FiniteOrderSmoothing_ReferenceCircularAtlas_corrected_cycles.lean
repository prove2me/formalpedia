-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_corrected_cycles
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_cycles
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:08:40.442894+00:00
-- url     : https://prove2.me/theorems/7803737e-59f6-4801-a27c-edf4b19c373b
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_cycles: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_cycles` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/CycleCorrectedGeometry.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/CycleCorrectedGeometry.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas`, with `open Set Filter Manifold Bundle`, `open scoped ContDiff Topology BigOperators`, `open SmallModes PhaseGeometry SurfaceJetCoordinates`):
--
--   ```lean
--   theorem corrected_cycles {F : M → Space}
--       (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
--       (href : gref.inner = g.inner-inducedTensor (r • F))
--       {phaseBound weightBound mapBound : ℝ}
--       (hphaseBound : 0 < phaseBound) (hweightBound : 0 < weightBound)
--       (hmapBound : 0 < mapBound)
--       {m : ℕ} (e : Fin m ≃ (d.B.centers × Fin 3)) :
--       ∃ (mapTol delta : ℝ) (W : ℕ → ℝ),
--         0 < mapTol ∧ mapTol ≤ mapBound ∧ 0 < delta ∧
--         (∀ i, delta ≤ d.radius i/2) ∧ (∀ j, 0 ≤ W j) ∧
--         ∀ N : ℕ, 0 < N →
--         ∃ q : CircularFamilyGeometry d.B (Fin (N*m)),
--           (∀ a, (q.curves a).index = (e a.modNat).1) ∧
--           (∀ a, q.outerRadius a = d.radius (e a.modNat).1) ∧
--           (∀ a, q.chartRadius a = d.radius (e a.modNat).1) ∧
--           (∀ a, q.convexPart a = d.L (e a.modNat).1) ∧
--           (∀ a, ‖q.linearPart a‖ ≤ ‖(d.P (e a.modNat).1).ξ‖+1) ∧
--           (∀ a, ‖q.linearPart a-(d.P (e a.modNat).1).ξ (e a.modNat).2‖ < phaseBound) ∧
--           (∀ k b j, d.B.WeightedBound 1 j (W j) (d.cycleWeights e q k b)) ∧
--           (∀ k b p, |d.cycleWeights e q k b p-d.B.weight b.1 p| < weightBound) ∧
--           ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
--             A.WeightedBound 1 1 mapTol (G-F) →
--           ∃ (f : Fin N → SmoothPrimitiveFamily (Fin m) (g.inner-inducedTensor (r • G)))
--             (D : CircularPrimitiveFamily d.B (Fin (N*m))),
--             (∀ k a, (f k).amplitude a = d.B.correctedPrimitiveAmplitude d.basis
--               (d.cycleWeights e q k) (d.perturbedPhases (d.cycleLinearParts e q k))
--               (g.inner-inducedTensor (r • G)) (e a)) ∧
--             (∀ k a, (f k).phase a = d.perturbedPhases (d.cycleLinearParts e q k) (e a)) ∧
--             D.curves = q.curves ∧ D.radius = q.radius ∧ D.outerRadius = q.outerRadius ∧
--             D.chartRadius = q.chartRadius ∧ D.linearPart = q.linearPart ∧ D.convexPart = q.convexPart ∧
--             (∀ a p, D.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) ∧
--             (∀ a, D.phase a = (f a.divNat).phase a.modNat) ∧
--             D.totalTensor = g.inner-inducedTensor (r • G)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor` and `OAI.ClosedSurfaceR4.SmallModes.Base` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularFamilyGeometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.totalTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.basis`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.cycleLinearParts`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.cycleWeights` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.perturbedPhases` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily.cycleAmplitude` and `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.isometric_immersion_of_spherical_immersion` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/CycleCorrectedGeometry.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_cycles)

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
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseGeometry SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

namespace ReferenceCircularAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cycleGeometryDualAdd
local instance cycleGeometryFiberNormed_rb48348_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance cycleGeometryFiberSpace_rb48348_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance cycleGeometryDualSmul_rb48348_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

local instance cycleGeometrySectionNormed_rb48348_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cycleGeometrySectionSpace_rb48348_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem corrected_cycles {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F))
    {phaseBound weightBound mapBound : ℝ}
    (hphaseBound : 0 < phaseBound) (hweightBound : 0 < weightBound)
    (hmapBound : 0 < mapBound)
    {m : ℕ} (e : Fin m ≃ (d.B.centers × Fin 3)) :
    ∃ (mapTol delta : ℝ) (W : ℕ → ℝ),
      0 < mapTol ∧ mapTol ≤ mapBound ∧ 0 < delta ∧
      (∀ i, delta ≤ d.radius i/2) ∧ (∀ j, 0 ≤ W j) ∧
      ∀ N : ℕ, 0 < N →
      ∃ q : CircularFamilyGeometry d.B (Fin (N*m)),
        (∀ a, (q.curves a).index = (e a.modNat).1) ∧
        (∀ a, q.outerRadius a = d.radius (e a.modNat).1) ∧
        (∀ a, q.chartRadius a = d.radius (e a.modNat).1) ∧
        (∀ a, q.convexPart a = d.L (e a.modNat).1) ∧
        (∀ a, ‖q.linearPart a‖ ≤ ‖(d.P (e a.modNat).1).ξ‖+1) ∧
        (∀ a, ‖q.linearPart a-(d.P (e a.modNat).1).ξ (e a.modNat).2‖ < phaseBound) ∧
        (∀ k b j, d.B.WeightedBound 1 j (W j) (d.cycleWeights e q k b)) ∧
        (∀ k b p, |d.cycleWeights e q k b p-d.B.weight b.1 p| < weightBound) ∧
        ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
          A.WeightedBound 1 1 mapTol (G-F) →
        ∃ (f : Fin N → SmoothPrimitiveFamily (Fin m) (g.inner-inducedTensor (r • G)))
          (D : CircularPrimitiveFamily d.B (Fin (N*m))),
          (∀ k a, (f k).amplitude a = d.B.correctedPrimitiveAmplitude d.basis
            (d.cycleWeights e q k) (d.perturbedPhases (d.cycleLinearParts e q k))
            (g.inner-inducedTensor (r • G)) (e a)) ∧
          (∀ k a, (f k).phase a = d.perturbedPhases (d.cycleLinearParts e q k) (e a)) ∧
          D.curves = q.curves ∧ D.radius = q.radius ∧ D.outerRadius = q.outerRadius ∧
          D.chartRadius = q.chartRadius ∧ D.linearPart = q.linearPart ∧ D.convexPart = q.convexPart ∧
          (∀ a p, D.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p) ∧
          (∀ a, D.phase a = (f a.divNat).phase a.modNat) ∧
          D.totalTensor = g.inner-inducedTensor (r • G) := by
  sorry

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
