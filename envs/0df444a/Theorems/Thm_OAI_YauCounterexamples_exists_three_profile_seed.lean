-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_three_profile_seed
-- name    : OAI.YauCounterexamples.exists_three_profile_seed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:07:37.368139+00:00
-- url     : https://prove2.me/theorems/a76ea66c-6300-4242-bbf7-8df845648525
-- title:
--   OAI.YauCounterexamples.exists_three_profile_seed: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_three_profile_seed` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeRobustProfileNormedSpace.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeRobustProfileNormedSpace.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold MeasureTheory Metric`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   theorem exists_three_profile_seed :
--       ∃ f : ThreeModel → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
--         f =ᶠ[𝓝 0] threeLogEnvelope threeProfileCenter threeEnvelopeExponent ∧
--         ∃ r>0, ∀ y ∈ closedBall 0 r,
--           coordinateMetricGradient (threeChartMetric threeBackgroundMetric threeProfileCenter) f y ≠ 0 ∧
--           actualProfileStrict (threeChartMetric threeBackgroundMetric threeProfileCenter) f y
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel` and `OAI.YauCounterexamples.threeProfileCenter` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.threeEnvelopeExponent` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.coordinateMetricGradient` and `OAI.YauCounterexamples.threeBackgroundMetric` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeCenterNormedSpace` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.actualProfileStrict` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.threeChartMetric` and `OAI.YauCounterexamples.threeLogEnvelope` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_robust_seed` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeRobustProfileNormedSpace.lean (declaration OAI.YauCounterexamples.exists_three_profile_seed)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
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
open Set Filter Function Manifold MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace

attribute [local instance] OAI.YauCounterexamples.threeCenterNormedSpace
local instance threeCenterContinuousSMul_rafedd3_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
theorem exists_three_profile_seed :
    ∃ f : ThreeModel → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      f =ᶠ[𝓝 0] threeLogEnvelope threeProfileCenter threeEnvelopeExponent ∧
      ∃ r>0, ∀ y ∈ closedBall 0 r,
        coordinateMetricGradient (threeChartMetric threeBackgroundMetric threeProfileCenter) f y ≠ 0 ∧
        actualProfileStrict (threeChartMetric threeBackgroundMetric threeProfileCenter) f y := by
  sorry

end

open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end
