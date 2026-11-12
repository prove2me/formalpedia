-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_CrosscapCoordinateStrip_normalized_defect_rectangle_framed
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.normalized_defect_rectangle_framed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:22:39.41929+00:00
-- url     : https://prove2.me/theorems/26c278c4-5200-4a2b-b826-57a740a70e62
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.normalized_defect_rectangle_framed (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.normalized_defect_rectangle_framed` of [lean/OAI/Geometry/SurfaceImmersion/Whitney/CrosscapFramedRectangle.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/CrosscapFramedRectangle.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open JetPolynomial (Base)`):
--
--   ```lean
--   theorem CrosscapCoordinateStrip.normalized_defect_rectangle_framed (S : CrosscapCoordinateStrip A)
--       (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
--       ∃ (a : Fin 3 → ℝ) (d : ℝ → Base) (r : ℝ) (O : Set Base),
--         ContDiff ℝ ∞ d ∧ 0 < r ∧ IsOpen O ∧ O ⊆ S.domain ∧
--         (∀ x ∈ Icc (-r) r, ∀ t ∈ Icc (A.arc.start-r) (A.arc.finish+r), (![x,t] : Base) ∈ O) ∧
--         ContDiffOn ℝ ∞ (axisNormalizedDefect d (normalDefect S.model a)) O ∧
--         (∀ t, crosscapAxis t ∈ O →
--           axisNormalizedDefect d (normalDefect S.model a) (crosscapAxis t) =
--             ![(t-A.arc.start)*(t-A.arc.finish),0]) ∧
--         (∀ x ∈ O, axisNormalizedDefect d (normalDefect S.model a) x = 0 ↔
--           x = crosscapAxis A.arc.start ∨ x = crosscapAxis A.arc.finish) ∧
--         Function.Bijective (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
--           (crosscapAxis A.arc.start)) ∧
--         Function.Bijective (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
--           (crosscapAxis A.arc.finish)) ∧
--         (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
--           (crosscapAxis A.arc.start) (![1,0] : Base)) 1 ≠ 0 ∧
--         (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
--           (crosscapAxis A.arc.finish) (![1,0] : Base)) 1 ≠ 0 ∧
--         (∀ x ∈ O, d (x 1) ≠ 0) ∧ O ⊆ normalFrameDomain S.model a
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ProjectionTarget` and `OAI.ClosedSurfaceR4.JetPolynomial.Base` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothCompactArc` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapConnectingArc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crosscapAxis` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.normalDefect` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.normalFrameDomain` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.axisNormalizedDefect` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.formal_pair` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/CrosscapFramedRectangle.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.normalized_defect_rectangle_framed)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI008

section

attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.normalized_defect_rectangle_framed (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    ∃ (a : Fin 3 → ℝ) (d : ℝ → Base) (r : ℝ) (O : Set Base),
      ContDiff ℝ ∞ d ∧ 0 < r ∧ IsOpen O ∧ O ⊆ S.domain ∧
      (∀ x ∈ Icc (-r) r, ∀ t ∈ Icc (A.arc.start-r) (A.arc.finish+r), (![x,t] : Base) ∈ O) ∧
      ContDiffOn ℝ ∞ (axisNormalizedDefect d (normalDefect S.model a)) O ∧
      (∀ t, crosscapAxis t ∈ O →
        axisNormalizedDefect d (normalDefect S.model a) (crosscapAxis t) =
          ![(t-A.arc.start)*(t-A.arc.finish),0]) ∧
      (∀ x ∈ O, axisNormalizedDefect d (normalDefect S.model a) x = 0 ↔
        x = crosscapAxis A.arc.start ∨ x = crosscapAxis A.arc.finish) ∧
      Function.Bijective (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
        (crosscapAxis A.arc.start)) ∧
      Function.Bijective (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
        (crosscapAxis A.arc.finish)) ∧
      (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
        (crosscapAxis A.arc.start) (![1,0] : Base)) 1 ≠ 0 ∧
      (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
        (crosscapAxis A.arc.finish) (![1,0] : Base)) 1 ≠ 0 ∧
      (∀ x ∈ O, d (x 1) ≠ 0) ∧ O ⊆ normalFrameDomain S.model a := by
  sorry

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
