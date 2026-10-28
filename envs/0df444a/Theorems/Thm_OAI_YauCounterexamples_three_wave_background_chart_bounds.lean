-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_three_wave_background_chart_bounds
-- name    : OAI.YauCounterexamples.three_wave_background_chart_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:14:35.737174+00:00
-- url     : https://prove2.me/theorems/38ef5314-b2f6-48e6-9b2e-230621d41b57
-- title:
--   OAI.YauCounterexamples.three_wave_background_chart_bounds: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.three_wave_background_chart_bounds` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem three_wave_background_chart_bounds
--       (g : SmoothMetric ThreeModel ThreeManifold)
--       {F : Set (ThreeManifold)} (hF : IsClosed F)
--       (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
--         g.inner q v w=threeBackgroundMetric.inner q v w)
--       {φ : ThreeManifold → ℝ} (hφ : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ φ)
--       {δ : ℝ} (hδ : 0<δ)
--       (hgap : ∀ q∈F, threeGlobalLog q+δ ≤ φ q)
--       (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K)
--       (r : ℝ) (m D : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
--       ∃ C > 0, ∀ᶠ n : ℕ in atTop,
--       ∀ (u : NormalWaveSpace → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
--         tsupport u ⊆ closedBall 0 r →
--         (∀ y : NormalWaveSpace, ∀ j ≤ m,
--           ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(n:ℝ)^(j+4)*
--             Real.exp (productWaveFrequency n*φ (threeNormalInv y)) ∧
--           ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+
--             productFrequency n*u y) y‖ ≤ C₀*((n:ℝ)^(D+1))⁻¹*
--             Real.exp (productWaveFrequency n*φ (threeNormalInv y))) →
--         ∀ y ∈ K, ∀ j ≤ m,
--           ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius n+threeWaveLift u) ∘
--             (chartAt ThreeModel p).symm) y‖ ≤
--             C*(n:ℝ)^(j+4)*threeWeight φ n ((chartAt ThreeModel p).symm y) ∧
--           ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
--             (threeCoupled threeCouplingRadius n+threeWaveLift u) q+
--             productFrequency n*(threeCoupled threeCouplingRadius n+threeWaveLift u) q) ∘
--             (chartAt ThreeModel p).symm) y‖ ≤
--             C*(n:ℝ)^4/(n:ℝ)^D*threeWeight φ n ((chartAt ThreeModel p).symm y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.productFrequency`, `OAI.YauCounterexamples.productWaveFrequency` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.threeBackgroundMetric` and `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeAssemblyNormedSpace` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.threeCoupled`, `OAI.YauCounterexamples.threeGlobalLog`, `OAI.YauCounterexamples.threeNormalMetricOf`, `OAI.YauCounterexamples.threeWaveLift` and `OAI.YauCounterexamples.threeWeight` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_global_quasimodes` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean (declaration OAI.YauCounterexamples.three_wave_background_chart_bounds)

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

attribute [local instance] OAI.YauCounterexamples.threeAssemblyNormedSpace
local instance threeAssemblyContinuousSMul_r55631b_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
theorem three_wave_background_chart_bounds
    (g : SmoothMetric ThreeModel ThreeManifold)
    {F : Set (ThreeManifold)} (hF : IsClosed F)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
      g.inner q v w=threeBackgroundMetric.inner q v w)
    {φ : ThreeManifold → ℝ} (hφ : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ φ)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ q∈F, threeGlobalLog q+δ ≤ φ q)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K)
    (r : ℝ) (m D : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
    ∀ (u : NormalWaveSpace → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ closedBall 0 r →
      (∀ y : NormalWaveSpace, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(n:ℝ)^(j+4)*
          Real.exp (productWaveFrequency n*φ (threeNormalInv y)) ∧
        ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+
          productFrequency n*u y) y‖ ≤ C₀*((n:ℝ)^(D+1))⁻¹*
          Real.exp (productWaveFrequency n*φ (threeNormalInv y))) →
      ∀ y ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius n+threeWaveLift u) ∘
          (chartAt ThreeModel p).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*threeWeight φ n ((chartAt ThreeModel p).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
          (threeCoupled threeCouplingRadius n+threeWaveLift u) q+
          productFrequency n*(threeCoupled threeCouplingRadius n+threeWaveLift u) q) ∘
          (chartAt ThreeModel p).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*threeWeight φ n ((chartAt ThreeModel p).symm y) := by
  sorry

end

open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

end YauCounterexamples
end

end OAI
end
