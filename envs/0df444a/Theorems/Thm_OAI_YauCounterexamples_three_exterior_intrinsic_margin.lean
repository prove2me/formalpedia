-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_three_exterior_intrinsic_margin
-- name    : OAI.YauCounterexamples.three_exterior_intrinsic_margin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:14:01.013983+00:00
-- url     : https://prove2.me/theorems/0fdbb4df-1565-4a92-bbd4-b32ffb391144
-- title:
--   OAI.YauCounterexamples.three_exterior_intrinsic_margin: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.three_exterior_intrinsic_margin` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma three_exterior_intrinsic_margin (g : SmoothMetric ThreeModel ThreeManifold)
--       {φ : ThreeManifold → ℝ} (r C₀ : ℝ) (hC₀ : 0<C₀) :
--       ∀ᶠ k : ℕ in atTop, ∀ u : NormalWaveSpace → ℝ,
--         ContDiff ℝ ∞ u → HasCompactSupport u → tsupport u⊆closedBall 0 r →
--         (∀ y : NormalWaveSpace, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(k:ℝ)^(j+4)*
--           Real.exp (productWaveFrequency k*φ (threeNormalInv y))) →
--         ∀ p∉threeExceptional φ k,
--         (∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) p, g.inner p v w=threeBackgroundMetric.inner p v w) →
--         let U := threeCoupled threeCouplingRadius k+threeWaveLift u
--         threeWeight φ k p/productWaveFrequency k^111 ≤ |U p|+
--           Real.sqrt (coordinateGradientPair g U U p)/productWaveFrequency k
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair`, `OAI.YauCounterexamples.productWaveFrequency` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.threeBackgroundMetric` and `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeCoupled`, `OAI.YauCounterexamples.threeExceptional`, `OAI.YauCounterexamples.threeWaveLift` and `OAI.YauCounterexamples.threeWeight` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_global_quasimodes` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean (declaration OAI.YauCounterexamples.three_exterior_intrinsic_margin)

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

lemma three_exterior_intrinsic_margin (g : SmoothMetric ThreeModel ThreeManifold)
    {φ : ThreeManifold → ℝ} (r C₀ : ℝ) (hC₀ : 0<C₀) :
    ∀ᶠ k : ℕ in atTop, ∀ u : NormalWaveSpace → ℝ,
      ContDiff ℝ ∞ u → HasCompactSupport u → tsupport u⊆closedBall 0 r →
      (∀ y : NormalWaveSpace, ∀ j ≤ 1, ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(k:ℝ)^(j+4)*
        Real.exp (productWaveFrequency k*φ (threeNormalInv y))) →
      ∀ p∉threeExceptional φ k,
      (∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) p, g.inner p v w=threeBackgroundMetric.inner p v w) →
      let U := threeCoupled threeCouplingRadius k+threeWaveLift u
      threeWeight φ k p/productWaveFrequency k^111 ≤ |U p|+
        Real.sqrt (coordinateGradientPair g U U p)/productWaveFrequency k := by
  sorry
end

open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

end YauCounterexamples
end

end OAI
end
