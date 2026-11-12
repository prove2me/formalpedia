-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_prepared_clean_crosscap_neighborhoods
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_clean_crosscap_neighborhoods
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:10:23.953594+00:00
-- url     : https://prove2.me/theorems/d3cfbc4f-bacb-4ade-9e99-8fe9e04a6ec6
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_clean_crosscap_neighborhoods: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_clean_crosscap_neighborhoods` of [lean/OAI/Geometry/SurfaceImmersion/Whitney/CleanCrosscapNeighborhoods.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/CleanCrosscapNeighborhoods.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing`, with `open Set Filter Manifold Topology`, `open scoped ContDiff`, `open JetPolynomial (Base)`):
--
--   ```lean
--   theorem prepared_clean_crosscap_neighborhoods
--       {f : M → ProjectionTarget 3}
--       (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
--       (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
--         ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
--           p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
--           f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
--           surfaceDirection φ b (chart q p,t) = 0 ∧
--           Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
--       let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
--       ∃ A : S → Set M, (∀ i, IsCompact (A i) ∧ i.val ∈ interior (A i)) ∧
--         Pairwise (fun i j => Disjoint (A i) (A j)) ∧
--         ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → (x,y) ∈ cleanSurfacePairs f S
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ProjectionTarget`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart` and `OAI.ClosedSurfaceR4.JetPolynomial.Base` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.centeredSurfaceTaylor` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.surfaceDirection` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cleanSurfacePairs` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_clean_finite_quadratic_map` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.remove_finite_quadratic_crosscaps` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/CleanCrosscapNeighborhoods.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_clean_crosscap_neighborhoods)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
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
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_clean_crosscap_neighborhoods
    {f : M → ProjectionTarget 3}
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
    ∃ A : S → Set M, (∀ i, IsCompact (A i) ∧ i.val ∈ interior (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → (x,y) ∈ cleanSurfacePairs f S := by
  sorry

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
