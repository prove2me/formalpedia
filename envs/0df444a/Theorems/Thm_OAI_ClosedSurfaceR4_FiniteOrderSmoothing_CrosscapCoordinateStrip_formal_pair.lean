-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_CrosscapCoordinateStrip_formal_pair
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.formal_pair
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:09:32.340762+00:00
-- url     : https://prove2.me/theorems/8f0c92d6-23e6-4013-b98c-1e533437418a
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.formal_pair: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.formal_pair` of [lean/OAI/Geometry/SurfaceImmersion/Whitney/CrosscapFormalPair.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/CrosscapFormalPair.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open JetPolynomial (Base)`):
--
--   ```lean
--   theorem CrosscapCoordinateStrip.formal_pair (S : CrosscapCoordinateStrip A)
--       (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
--       ∃ (V : Set Base) (B : Base → Base →L[ℝ] ProjectionTarget 3) (K : Set Base),
--         IsOpen V ∧ V ⊆ S.domain ∧
--         (∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ V) ∧
--         ContDiff ℝ ∞ B ∧ IsCompact K ∧ K ⊆ V ∧ tsupport (B-fderiv ℝ S.model) ⊆ K ∧
--         (∀ x ∈ V, Function.Injective (B x)) ∧
--         ∀ x ∈ V, Function.Injective (fderiv ℝ S.model x) ↔
--           x ≠ crosscapAxis A.arc.start ∧ x ≠ crosscapAxis A.arc.finish
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ProjectionTarget` and `OAI.ClosedSurfaceR4.JetPolynomial.Base` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothCompactArc` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapConnectingArc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crosscapAxis` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cancel_crosscap_pair` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/CrosscapFormalPair.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.formal_pair)

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
import Definitions.Def_OAIQ249SI004

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

theorem CrosscapCoordinateStrip.formal_pair (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    ∃ (V : Set Base) (B : Base → Base →L[ℝ] ProjectionTarget 3) (K : Set Base),
      IsOpen V ∧ V ⊆ S.domain ∧
      (∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ V) ∧
      ContDiff ℝ ∞ B ∧ IsCompact K ∧ K ⊆ V ∧ tsupport (B-fderiv ℝ S.model) ⊆ K ∧
      (∀ x ∈ V, Function.Injective (B x)) ∧
      ∀ x ∈ V, Function.Injective (fderiv ℝ S.model x) ↔
        x ≠ crosscapAxis A.arc.start ∧ x ≠ crosscapAxis A.arc.finish := by
  sorry

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
