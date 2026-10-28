-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_global_spherical_wave_profile
-- name    : OAI.YauCounterexamples.exists_global_spherical_wave_profile
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:02:20.421732+00:00
-- url     : https://prove2.me/theorems/140febd4-1ba6-48bd-bf13-1f6d3b6afd0e
-- title:
--   OAI.YauCounterexamples.exists_global_spherical_wave_profile: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_global_spherical_wave_profile` of [lean/OAI/Geometry/SmoothYau/Smoothness/SourceSignBox.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/SourceSignBox.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter Metric`, `open scoped Topology InnerProductSpace`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Manifold`, `open scoped Topology ContDiff`, `open Set Filter Manifold MeasureTheory BoxIntegral`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem exists_global_spherical_wave_profile
--       (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
--       (t : ℝ) (ht : t ∈ Icc (1/5 : ℝ) (3/10)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
--       ∃ φ : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ ∧
--         tsupport (fun q => φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q) ⊆ sourceSignRegion ∧
--         (∀ q, |φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q| < ε) ∧
--         (∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
--           sphericalRadius sourceAxisOne sourceAxisTwo q < t →
--           Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q) ∧
--         (∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
--           φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) ∧
--         (∀ y ∈ sourceProfileCoverage, fderiv ℝ (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y ≠ 0 →
--           actualProfileStrict (sphereChartMetric g sourcePole)
--             (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y) ∧
--         (∀ y ∈ sourceProfileCoverage, fderiv ℝ (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y = 0 →
--           ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
--             ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian (sphereChartMetric g sourcePole)
--               (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y v v) ∧
--         (∀ y ∈ normalWaveEquiv '' Box.Icc sourceSignBox,
--           coordinateMetricGradient (sphereChartMetric g sourcePole)
--             (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y ≠ 0 ∧
--           actualProfileStrict (sphereChartMetric g sourcePole)
--             (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y) ∧
--         T < ∫ x in Box.Icc sourceSignBox, profileFrequencyScale (sphereChartMetric g sourcePole)
--           (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) (normalWaveEquiv x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CoordinateForm`, `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.actualCoordinateHessian`, `OAI.YauCounterexamples.normalWaveEquiv`, `OAI.YauCounterexamples.sourceAxisOne`, `OAI.YauCounterexamples.sourceAxisTwo`, `OAI.YauCounterexamples.sourcePole`, `OAI.YauCounterexamples.sourceProfileCoverage`, `OAI.YauCounterexamples.sourceSignBox`, `OAI.YauCounterexamples.sphericalBaseProfile` and `OAI.YauCounterexamples.sphericalRadius` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.coordinateMetricGradient`, `OAI.YauCounterexamples.sphereChartMetric` and `OAI.YauCounterexamples.sphericalProfileMetricNeighborhood` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.sourceSignRegion` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.actualProfileStrict` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.profileFrequencyScale` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_chart_quasimodes` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/SourceSignBox.lean (declaration OAI.YauCounterexamples.exists_global_spherical_wave_profile)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010

section

attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter Manifold MeasureTheory BoxIntegral
open scoped Topology ContDiff
namespace YauCounterexamples

theorem exists_global_spherical_wave_profile
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    (t : ℝ) (ht : t ∈ Icc (1/5 : ℝ) (3/10)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ ∧
      tsupport (fun q => φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q) ⊆ sourceSignRegion ∧
      (∀ q, |φ q-sphericalBaseProfile sourceAxisOne sourceAxisTwo t q| < ε) ∧
      (∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
        sphericalRadius sourceAxisOne sourceAxisTwo q < t →
        Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q) ∧
      (∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
        φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) ∧
      (∀ y ∈ sourceProfileCoverage, fderiv ℝ (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y ≠ 0 →
        actualProfileStrict (sphereChartMetric g sourcePole)
          (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y) ∧
      (∀ y ∈ sourceProfileCoverage, fderiv ℝ (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y = 0 →
        ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
          ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian (sphereChartMetric g sourcePole)
            (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y v v) ∧
      (∀ y ∈ normalWaveEquiv '' Box.Icc sourceSignBox,
        coordinateMetricGradient (sphereChartMetric g sourcePole)
          (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y ≠ 0 ∧
        actualProfileStrict (sphereChartMetric g sourcePole)
          (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) y) ∧
      T < ∫ x in Box.Icc sourceSignBox, profileFrequencyScale (sphereChartMetric g sourcePole)
        (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) (normalWaveEquiv x) := by
  sorry

end YauCounterexamples

end

end OAI
end
