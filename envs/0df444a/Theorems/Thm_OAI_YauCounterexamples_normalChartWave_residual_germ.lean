-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_normalChartWave_residual_germ
-- name    : OAI.YauCounterexamples.normalChartWave_residual_germ
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:45:29.880542+00:00
-- url     : https://prove2.me/theorems/de9c9705-8dfc-49d5-bcfd-0bde4e9acf37
-- title:
--   OAI.YauCounterexamples.normalChartWave_residual_germ: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.normalChartWave_residual_germ` of [lean/OAI/Geometry/SmoothYau/Geometry/NormalWaveMetricCommonPositive.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/NormalWaveMetricCommonPositive.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Matrix`, `open scoped Topology Matrix.Norms.Elementwise`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter Matrix`, `open scoped Topology ContDiff Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem normalChartWave_residual_germ (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       (q : NormalWaveParameter) (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
--       (he : (e : NormalWaveSpace → NormalWaveSpace) =
--         normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2))
--       {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
--       (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source)
--       (hi : ContDiffOn ℝ ∞ e.symm e.target)
--       (A : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
--       (lam : ℂ) {R : ℝ}
--       (hp : ∀ v : NormalWaveSpace, ‖v‖ < R → 0 < (normalWaveMetric g q v).det)
--       (hA : ∀ x, ‖normalWaveEquiv x‖ < R → ∀ i j,
--         A i j x = ((normalWaveMetric g q (normalWaveEquiv x))⁻¹ i j : ℂ))
--       (hb : ∀ x, ‖normalWaveEquiv x‖ < R → ∀ j,
--         b j x = (normalWaveFirstCoefficient g q (normalWaveEquiv x) j : ℂ))
--       {x : Fin 3 → ℝ} (hx : normalWaveEquiv x ∈ e.source) (hxR : ‖normalWaveEquiv x‖ < R) :
--       (fun y => complexLaplaceBeltrami g (normalChartWave e f) y + lam*normalChartWave e f y)
--         =ᶠ[𝓝 (e (normalWaveEquiv x))] (fun y =>
--           waveCoordinateOperator (fun i => Pi.single i 1) A b f (normalWaveEquiv.symm (e.symm y)) +
--             lam*f (normalWaveEquiv.symm (e.symm y)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveParameter`, `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.complexLaplaceBeltrami`, `OAI.YauCounterexamples.metricChristoffel` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.normalJetMap` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.normalChartWave`, `OAI.YauCounterexamples.normalWaveFirstCoefficient`, `OAI.YauCounterexamples.normalWaveMetric` and `OAI.YauCounterexamples.waveCoordinateOperator` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/NormalWaveMetricCommonPositive.lean (declaration OAI.YauCounterexamples.normalChartWave_residual_germ)

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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples

theorem normalChartWave_residual_germ (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (he : (e : NormalWaveSpace → NormalWaveSpace) =
      normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2))
    {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (A : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (lam : ℂ) {R : ℝ}
    (hp : ∀ v : NormalWaveSpace, ‖v‖ < R → 0 < (normalWaveMetric g q v).det)
    (hA : ∀ x, ‖normalWaveEquiv x‖ < R → ∀ i j,
      A i j x = ((normalWaveMetric g q (normalWaveEquiv x))⁻¹ i j : ℂ))
    (hb : ∀ x, ‖normalWaveEquiv x‖ < R → ∀ j,
      b j x = (normalWaveFirstCoefficient g q (normalWaveEquiv x) j : ℂ))
    {x : Fin 3 → ℝ} (hx : normalWaveEquiv x ∈ e.source) (hxR : ‖normalWaveEquiv x‖ < R) :
    (fun y => complexLaplaceBeltrami g (normalChartWave e f) y + lam*normalChartWave e f y)
      =ᶠ[𝓝 (e (normalWaveEquiv x))] (fun y =>
        waveCoordinateOperator (fun i => Pi.single i 1) A b f (normalWaveEquiv.symm (e.symm y)) +
          lam*f (normalWaveEquiv.symm (e.symm y))) := by
  sorry
end YauCounterexamples
end

end OAI
end
