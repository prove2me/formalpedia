-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_prepared_smooth_crosscap_arc
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_smooth_crosscap_arc
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:11:00.094867+00:00
-- url     : https://prove2.me/theorems/6c4ac88d-8789-4775-9cff-34212098d597
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_smooth_crosscap_arc: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_smooth_crosscap_arc` of [lean/OAI/Geometry/SurfaceImmersion/Whitney/PreparedSmoothCrosscapArc.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/PreparedSmoothCrosscapArc.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing`, with `open Set Filter Manifold Topology unitInterval`, `open scoped ContDiff`, `open JetPolynomial (Base)`):
--
--   ```lean
--   theorem prepared_smooth_crosscap_arc {f : M → ProjectionTarget 3}
--       (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
--       (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
--       (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
--       (hsimple : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
--         ∀ q, f q = f p → q = p)
--       (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
--         ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
--           p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
--           f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
--           surfaceDirection φ b (chart q p,t) = 0 ∧
--           Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
--       (p : M) (hp : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
--       ∃ (q : M) (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
--         (P : SmoothCompactArc planeModel M) (V W : Set M),
--         q ≠ p ∧ ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f q) ∧
--         IsOpen V ∧ p ∈ V ∧ IsOpen W ∧ q ∈ W ∧
--         P.curve P.start = p ∧ P.curve P.finish = q ∧
--         (∀ t ∈ Ioo P.start P.finish,
--           Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P.curve t))) ∧
--         (∀ t ∈ Icc P.start P.finish, P.curve t ∈ V →
--           P.curve t ∈ cp.source.source ∧ cp.source (P.curve t) 0 = 0) ∧
--         (∀ t ∈ Icc P.start P.finish, P.curve t ∈ W →
--           P.curve t ∈ cq.source.source ∧ cq.source (P.curve t) 0 = 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ProjectionTarget`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart` and `OAI.ClosedSurfaceR4.JetPolynomial.Base` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothCompactArc` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SurfaceCrosscapCoordinates`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.centeredSurfaceTaylor` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.surfaceDirection` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.surfacePairDerivative` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.remove_finite_quadratic_crosscaps` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/PreparedSmoothCrosscapArc.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_smooth_crosscap_arc)

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
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI004
import Definitions.Def_OAIQ249SI005

section

attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Topology unitInterval
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_smooth_crosscap_arc {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (hsimple : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∀ q, f q = f p → q = p)
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
    (p : M) (hp : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
    ∃ (q : M) (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
      (P : SmoothCompactArc planeModel M) (V W : Set M),
      q ≠ p ∧ ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f q) ∧
      IsOpen V ∧ p ∈ V ∧ IsOpen W ∧ q ∈ W ∧
      P.curve P.start = p ∧ P.curve P.finish = q ∧
      (∀ t ∈ Ioo P.start P.finish,
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P.curve t))) ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ V →
        P.curve t ∈ cp.source.source ∧ cp.source (P.curve t) 0 = 0) ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ W →
        P.curve t ∈ cq.source.source ∧ cq.source (P.curve t) 0 = 0) := by
  sorry

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
