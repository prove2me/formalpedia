-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_threeCoupled_global_residual_rapid_decay
-- name    : OAI.YauCounterexamples.threeCoupled_global_residual_rapid_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:11:08.321487+00:00
-- url     : https://prove2.me/theorems/a724972c-31c8-466d-8c15-b8cb6f7e3b71
-- title:
--   OAI.YauCounterexamples.threeCoupled_global_residual_rapid_decay: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.threeCoupled_global_residual_rapid_decay` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem threeCoupled_global_residual_rapid_decay
--       (g : SmoothMetric ThreeModel ThreeManifold) {F : Set ThreeManifold} (hF : IsClosed F)
--       (hext : ∀ p ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) p,
--         g.inner p v w=threeBackgroundMetric.inner p v w)
--       {φ : ThreeManifold → ℝ} (hφ : Continuous φ) {δ : ℝ} (hδ : 0<δ)
--       (hgap : ∀ p∈F, threeGlobalLog p+δ ≤ φ p)
--       (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (h P : ℕ) :
--       ∃ N : ℕ, 2 ≤ N ∧ ∀ k≥N, ∀ y∈K, ∀ j ≤ h,
--         ‖iteratedFDeriv ℝ j ((fun z => laplaceBeltrami g (threeCoupled threeCouplingRadius k) z+
--           productFrequency k*threeCoupled threeCouplingRadius k z) ∘ (chartAt ThreeModel p).symm) y‖ ≤
--             ((k:ℝ)^P)⁻¹*Real.exp (productWaveFrequency k*φ ((chartAt ThreeModel p).symm y))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.productFrequency`, `OAI.YauCounterexamples.productWaveFrequency` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.threeBackgroundMetric` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeGlobalResidualNormedSpace` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.threeCoupled` and `OAI.YauCounterexamples.threeGlobalLog` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.three_wave_background_chart_bounds` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean (declaration OAI.YauCounterexamples.threeCoupled_global_residual_rapid_decay)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff

attribute [local instance] OAI.YauCounterexamples.threeGlobalResidualNormedSpace
local instance threeGlobalResidualContinuousSMul_rbd33bd_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
theorem threeCoupled_global_residual_rapid_decay
    (g : SmoothMetric ThreeModel ThreeManifold) {F : Set ThreeManifold} (hF : IsClosed F)
    (hext : ∀ p ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) p,
      g.inner p v w=threeBackgroundMetric.inner p v w)
    {φ : ThreeManifold → ℝ} (hφ : Continuous φ) {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ p∈F, threeGlobalLog p+δ ≤ φ p)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (h P : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ k≥N, ∀ y∈K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j ((fun z => laplaceBeltrami g (threeCoupled threeCouplingRadius k) z+
        productFrequency k*threeCoupled threeCouplingRadius k z) ∘ (chartAt ThreeModel p).symm) y‖ ≤
          ((k:ℝ)^P)⁻¹*Real.exp (productWaveFrequency k*φ ((chartAt ThreeModel p).symm y)) := by
  sorry
end

open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

end YauCounterexamples
end

end OAI
end
