-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_three_clean_collar_gradient
-- name    : OAI.YauCounterexamples.three_clean_collar_gradient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:13:08.934692+00:00
-- url     : https://prove2.me/theorems/fc15fe33-6020-42a2-818d-2c75e156c5c7
-- title:
--   OAI.YauCounterexamples.three_clean_collar_gradient: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.three_clean_collar_gradient` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric`, `open scoped Topology ContDiff Distributions ENNReal NNReal`):
--
--   ```lean
--   lemma three_clean_collar_gradient
--       (g : SmoothMetric ThreeModel ThreeManifold) {R b c : ℝ} (hR : 0<R)
--       (hclean : ThreeCleanBall R) (hc : c<R/2) (he : ThreeExterior g b)
--       (k : ℕ) (hk : 1 ≤ k) (u : ThreeManifold → ℝ)
--       (hu : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius k q) :
--       ∀ q∈threeCollar b c, 0 < coordinateGradientPair g u u q
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.ThreeCleanBall`, `OAI.YauCounterexamples.ThreeExterior` and `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeCollar` and `OAI.YauCounterexamples.threeCoupled` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.three_pin_near` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean (declaration OAI.YauCounterexamples.three_clean_collar_gradient)

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
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions ENNReal NNReal
lemma three_clean_collar_gradient
    (g : SmoothMetric ThreeModel ThreeManifold) {R b c : ℝ} (hR : 0<R)
    (hclean : ThreeCleanBall R) (hc : c<R/2) (he : ThreeExterior g b)
    (k : ℕ) (hk : 1 ≤ k) (u : ThreeManifold → ℝ)
    (hu : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius k q) :
    ∀ q∈threeCollar b c, 0 < coordinateGradientPair g u u q := by
  sorry
end

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end
