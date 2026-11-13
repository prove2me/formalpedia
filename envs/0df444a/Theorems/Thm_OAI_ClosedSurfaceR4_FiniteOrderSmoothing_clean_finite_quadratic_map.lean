-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_clean_finite_quadratic_map
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.clean_finite_quadratic_map
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T09:41:25.152679+00:00
-- url     : https://prove2.me/theorems/42ba84fa-c198-4cfc-a50b-1c04767589c1
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.clean_finite_quadratic_map: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.clean_finite_quadratic_map` of [lean/OAI/Geometry/SurfaceImmersion/Whitney/FiniteCrosscapCleanup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/FiniteCrosscapCleanup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open JetPolynomial (Base)`):
--
--   ```lean
--   theorem clean_finite_quadratic_map {f : M → ProjectionTarget 3}
--       (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
--       (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
--       (hrep : QuadraticCrosscapGerms f) :
--       ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
--         (∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p) ↔
--           Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) ∧
--         (∀ x y, x ≠ y → g x = g y → Function.Surjective (surfacePairDerivative g x y)) ∧
--         (∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p) →
--           ∀ q, g q = g p → q = p) ∧ QuadraticCrosscapGerms g
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ProjectionTarget` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.QuadraticCrosscapGerms` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.surfacePairDerivative` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.PublishedInputs.whitneySurfaceInput` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/FiniteCrosscapCleanup.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.clean_finite_quadratic_map)

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
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem clean_finite_quadratic_map {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hrep : QuadraticCrosscapGerms f) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      (∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p) ↔
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) ∧
      (∀ x y, x ≠ y → g x = g y → Function.Surjective (surfacePairDerivative g x y)) ∧
      (∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p) →
        ∀ q, g q = g p → q = p) ∧ QuadraticCrosscapGerms g := by
  sorry

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
