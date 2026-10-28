-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_normal_wave_chart_family
-- name    : OAI.YauCounterexamples.exists_normal_wave_chart_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:41:11.867689+00:00
-- url     : https://prove2.me/theorems/6825cae5-1829-4603-872c-5ce22c8c9698
-- title:
--   OAI.YauCounterexamples.exists_normal_wave_chart_family: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_normal_wave_chart_family` of [lean/OAI/Geometry/SmoothYau/Limits/CompactFiberLocalCompBound.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CompactFiberLocalCompBound.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Matrix`, `open scoped Topology Matrix.Norms.Elementwise`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem exists_normal_wave_chart_family (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       {K : Set NormalWaveSpace} (hK : IsCompact K) :
--       ∃ r > 0, ∃ e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace,
--         (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
--           normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
--         (∀ q, ContDiffOn ℝ ∞ (e q).symm (e q).target) ∧
--         (∀ q ∈ metricFrameSet g K, Metric.closedBall (0 : NormalWaveSpace) r ⊆ (e q).source) ∧
--         ∃ ψ : NormalWaveParameter × NormalWaveSpace → NormalWaveSpace, ContDiff ℝ ∞ ψ ∧
--           ∀ q ∈ metricFrameSet g K, ∀ x ∈ Metric.closedBall (0 : NormalWaveSpace) r,
--             (e q).symm =ᶠ[𝓝 (e q x)] (fun y => ψ (q,y))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveParameter`, `OAI.YauCounterexamples.NormalWaveSpace` and `OAI.YauCounterexamples.metricChristoffel` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.normalJetMap` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.metricFrameSet` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CompactFiberLocalCompBound.lean (declaration OAI.YauCounterexamples.exists_normal_wave_chart_family)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

theorem exists_normal_wave_chart_family (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ r > 0, ∃ e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace,
      (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
        normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
      (∀ q, ContDiffOn ℝ ∞ (e q).symm (e q).target) ∧
      (∀ q ∈ metricFrameSet g K, Metric.closedBall (0 : NormalWaveSpace) r ⊆ (e q).source) ∧
      ∃ ψ : NormalWaveParameter × NormalWaveSpace → NormalWaveSpace, ContDiff ℝ ∞ ψ ∧
        ∀ q ∈ metricFrameSet g K, ∀ x ∈ Metric.closedBall (0 : NormalWaveSpace) r,
          (e q).symm =ᶠ[𝓝 (e q x)] (fun y => ψ (q,y)) := by
  sorry
end YauCounterexamples

end

end OAI
end
