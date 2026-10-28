-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_realSpectralResolvent_compact
-- name    : OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_compact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:52:51.136705+00:00
-- url     : https://prove2.me/theorems/7eb71e59-f05d-4f2a-9748-e368dd137835
-- title:
--   OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_compact: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_compact` of [lean/OAI/Geometry/SmoothYau/Spectrum/ContinuousEigenpairLinearization.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/ContinuousEigenpairLinearization.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples.CompactMetricAtlas`, with `open Set Filter Function`, `open scoped Topology ContDiff Manifold SchwartzMap`, `open Set Filter Manifold Bundle MeasureTheory NNReal`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Topology NNReal`, `open Set Filter Module`, `open scoped Topology`, `open Set Filter MeasureTheory Manifold Function`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma realSpectralResolvent_compact (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
--       (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
--       (he : A.errorBound B α ≤ 1 / 2) :
--       IsCompactOperator (A.realSpectralResolvent B α hα0 hα he)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CompactMetricAtlas`, `OAI.YauCounterexamples.FourierSobolevSpace`, `OAI.YauCounterexamples.CompactMetricAtlas.H`, `OAI.YauCounterexamples.CompactMetricAtlas.PatchCoefficients` and `OAI.YauCounterexamples.LocalMetricInverse` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.CompactMetricAtlas.errorBound`, `OAI.YauCounterexamples.CompactMetricAtlas.realH` and `OAI.YauCounterexamples.CompactMetricAtlas.realH_mod` (definitions bundle `OAIQ070A005` of this split); `OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple`, `OAI.YauCounterexamples.CompactMetricAtlas.actual_simple_eigenpair_persistence`, `OAI.YauCounterexamples.exists_annular_simple_pinned_family`, `OAI.YauCounterexamples.exists_three_simple_pinned_family`, `OAI_YauCounterexamples_spherical_simple_eigenpair_open` and `OAI_YauCounterexamples_three_largeWitness_eventually` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/ContinuousEigenpairLinearization.lean (declaration OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_compact)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009

section

attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

lemma realSpectralResolvent_compact (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) :
    IsCompactOperator (A.realSpectralResolvent B α hα0 hα he) := by
  sorry
end CompactMetricAtlas

end

open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology

end YauCounterexamples
end

end OAI
end
