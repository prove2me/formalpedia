-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_normalChartWave_laplacian
-- name    : OAI.YauCounterexamples.normalChartWave_laplacian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:45:01.083032+00:00
-- url     : https://prove2.me/theorems/8fce689e-011b-479d-aafc-166ca18bb4df
-- title:
--   OAI.YauCounterexamples.normalChartWave_laplacian: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.normalChartWave_laplacian` of [lean/OAI/Geometry/SmoothYau/Smoothness/NormalChartWave.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/NormalChartWave.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Matrix`, `open scoped Topology Matrix.Norms.Elementwise`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem normalChartWave_laplacian (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       (q : NormalWaveParameter) (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
--       (he : (e : NormalWaveSpace → NormalWaveSpace) =
--         normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2))
--       {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
--       (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source)
--       (hi : ContDiffOn ℝ ∞ e.symm e.target) {x : Fin 3 → ℝ}
--       (hx : normalWaveEquiv x ∈ e.source)
--       (hp : 0 < (normalWaveMetric g q (normalWaveEquiv x)).det) :
--       complexLaplaceBeltrami g (normalChartWave e f) (e (normalWaveEquiv x)) =
--         normalWavePiOperator g q f x
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveParameter`, `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.complexLaplaceBeltrami`, `OAI.YauCounterexamples.metricChristoffel` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.normalJetMap` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.normalChartWave`, `OAI.YauCounterexamples.normalWaveMetric` and `OAI.YauCounterexamples.normalWavePiOperator` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.normalChartWave_residual_germ` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/NormalChartWave.lean (declaration OAI.YauCounterexamples.normalChartWave_laplacian)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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

theorem normalChartWave_laplacian (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (he : (e : NormalWaveSpace → NormalWaveSpace) =
      normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2))
    {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) {x : Fin 3 → ℝ}
    (hx : normalWaveEquiv x ∈ e.source)
    (hp : 0 < (normalWaveMetric g q (normalWaveEquiv x)).det) :
    complexLaplaceBeltrami g (normalChartWave e f) (e (normalWaveEquiv x)) =
      normalWavePiOperator g q f x := by
  sorry

end YauCounterexamples
end

end OAI
end
