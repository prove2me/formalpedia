-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_three_wave_lift_jets
-- name    : OAI.YauCounterexamples.three_wave_lift_jets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:14:53.379255+00:00
-- url     : https://prove2.me/theorems/5930ffaa-ecfe-468e-8d2c-b9446e97a5b2
-- title:
--   OAI.YauCounterexamples.three_wave_lift_jets: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.three_wave_lift_jets` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem three_wave_lift_jets (g : SmoothMetric ThreeModel ThreeManifold)
--       (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (r : ℝ) (m : ℕ) :
--       ∃ C>0, ∀ (u : NormalWaveSpace → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
--         tsupport u⊆closedBall 0 r →
--         ∀ (B : ℕ → ThreeManifold → ℝ), (∀ j q, 0 ≤ B j q) →
--         ∀ (R : ThreeManifold → ℝ), (∀ q, 0 ≤ R q) → ∀ Λ : ℝ,
--         (∀ x : NormalWaveSpace, ∀ j  ≤  m, ∀ i  ≤  j,
--           ‖iteratedFDeriv ℝ i u x‖ ≤ B j (threeNormalInv x)) →
--         (∀ x : NormalWaveSpace, ∀ j  ≤  m,
--           ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+Λ*u y) x‖ ≤ R (threeNormalInv x)) →
--         ∀ y∈K, ∀ j  ≤  m,
--           ‖iteratedFDeriv ℝ j (threeWaveLift u ∘ (chartAt ThreeModel p).symm) y‖ ≤ C*B j ((chartAt ThreeModel p).symm y) ∧
--           ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g (threeWaveLift u) q+Λ*threeWaveLift u q) ∘
--             (chartAt ThreeModel p).symm) y‖ ≤ C*R ((chartAt ThreeModel p).symm y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeLiftNormedSpace` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.threeNormalMetricOf` and `OAI.YauCounterexamples.threeWaveLift` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.three_wave_background_chart_bounds` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean (declaration OAI.YauCounterexamples.three_wave_lift_jets)

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

attribute [local instance] OAI.YauCounterexamples.threeLiftNormedSpace
local instance threeLiftContinuousSMul_ra47b4d_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
theorem three_wave_lift_jets (g : SmoothMetric ThreeModel ThreeManifold)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (r : ℝ) (m : ℕ) :
    ∃ C>0, ∀ (u : NormalWaveSpace → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u⊆closedBall 0 r →
      ∀ (B : ℕ → ThreeManifold → ℝ), (∀ j q, 0 ≤ B j q) →
      ∀ (R : ThreeManifold → ℝ), (∀ q, 0 ≤ R q) → ∀ Λ : ℝ,
      (∀ x : NormalWaveSpace, ∀ j  ≤  m, ∀ i  ≤  j,
        ‖iteratedFDeriv ℝ i u x‖ ≤ B j (threeNormalInv x)) →
      (∀ x : NormalWaveSpace, ∀ j  ≤  m,
        ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+Λ*u y) x‖ ≤ R (threeNormalInv x)) →
      ∀ y∈K, ∀ j  ≤  m,
        ‖iteratedFDeriv ℝ j (threeWaveLift u ∘ (chartAt ThreeModel p).symm) y‖ ≤ C*B j ((chartAt ThreeModel p).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g (threeWaveLift u) q+Λ*threeWaveLift u q) ∘
          (chartAt ThreeModel p).symm) y‖ ≤ C*R ((chartAt ThreeModel p).symm y) := by
  sorry
end

open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

end YauCounterexamples
end

end OAI
end
