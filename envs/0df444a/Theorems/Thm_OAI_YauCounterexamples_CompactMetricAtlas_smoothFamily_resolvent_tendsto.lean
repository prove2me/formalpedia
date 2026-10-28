-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_smoothFamily_resolvent_tendsto
-- name    : OAI.YauCounterexamples.CompactMetricAtlas.smoothFamily_resolvent_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:53:07.531281+00:00
-- url     : https://prove2.me/theorems/0439cd06-db54-4cfb-8c69-bfe068850608
-- title:
--   OAI.YauCounterexamples.CompactMetricAtlas.smoothFamily_resolvent_tendsto: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.CompactMetricAtlas.smoothFamily_resolvent_tendsto` of [lean/OAI/Geometry/SmoothYau/Spectrum/VaryingSpectralResolventBase.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/VaryingSpectralResolventBase.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples.CompactMetricAtlas`, with `open Set Filter Function Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   theorem smoothFamily_resolvent_tendsto
--       (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
--       (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
--       (q : ℝ → SmoothMetric E M) (hq0 : q 0 = g)
--       (hq : ∀ i t y, y ∈ (chartAt E (A.p i)).target → ∀ j l,
--         ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) (A.p i) z.2 j l) (t,y))
--       (C : ∀ t i, A.VaryingPatchCoefficients (q t) i) :
--       (∀ᶠ t in 𝓝 (0:ℝ), IsUnit (A.varyingShift (q t) (C t) α ∘L A.realResolvent B α hα0 hα he)) ∧
--       Tendsto (fun t => A.varyingSpectralResolvent B α hα0 hα he (q t) (C t)) (𝓝 (0:ℝ))
--         (𝓝 (A.realSpectralResolvent B α hα0 hα he))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CompactMetricAtlas`, `OAI.YauCounterexamples.FourierSobolevSpace`, `OAI.YauCounterexamples.CompactMetricAtlas.H`, `OAI.YauCounterexamples.CompactMetricAtlas.PatchCoefficients`, `OAI.YauCounterexamples.CompactMetricAtlas.VaryingPatchCoefficients`, `OAI.YauCounterexamples.CompactMetricAtlas.p` and `OAI.YauCounterexamples.LocalMetricInverse` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.CompactMetricAtlas.errorBound`, `OAI.YauCounterexamples.CompactMetricAtlas.realH`, `OAI.YauCounterexamples.CompactMetricAtlas.realH_acg` and `OAI.YauCounterexamples.CompactMetricAtlas.realH_mod` (definitions bundle `OAIQ070A005` of this split); `OAI.YauCounterexamples.CompactMetricAtlas.realResolvent`, `OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent`, `OAI.YauCounterexamples.CompactMetricAtlas.varyingShift` and `OAI.YauCounterexamples.CompactMetricAtlas.varyingSpectralResolvent` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.CoordIndex`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.metricCoefficients` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.CompactMetricAtlas.actual_pinned_eventually_simple` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/VaryingSpectralResolventBase.lean (declaration OAI.YauCounterexamples.CompactMetricAtlas.smoothFamily_resolvent_tendsto)

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
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem smoothFamily_resolvent_tendsto
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (q : ℝ → SmoothMetric E M) (hq0 : q 0 = g)
    (hq : ∀ i t y, y ∈ (chartAt E (A.p i)).target → ∀ j l,
      ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) (A.p i) z.2 j l) (t,y))
    (C : ∀ t i, A.VaryingPatchCoefficients (q t) i) :
    (∀ᶠ t in 𝓝 (0:ℝ), IsUnit (A.varyingShift (q t) (C t) α ∘L A.realResolvent B α hα0 hα he)) ∧
    Tendsto (fun t => A.varyingSpectralResolvent B α hα0 hα he (q t) (C t)) (𝓝 (0:ℝ))
      (𝓝 (A.realSpectralResolvent B α hα0 hα he)) := by
  sorry
end CompactMetricAtlas
end

open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end
