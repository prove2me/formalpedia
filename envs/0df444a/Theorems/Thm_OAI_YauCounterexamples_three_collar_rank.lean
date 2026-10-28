-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_three_collar_rank
-- name    : OAI.YauCounterexamples.three_collar_rank
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:13:38.773311+00:00
-- url     : https://prove2.me/theorems/75cfd882-8809-4728-99bc-33e905f7645c
-- title:
--   OAI.YauCounterexamples.three_collar_rank: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.three_collar_rank` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric`, `open scoped Topology ContDiff Distributions ENNReal NNReal`):
--
--   ```lean
--   lemma three_collar_rank
--       (g : SmoothMetric ThreeModel ThreeManifold) {b c : ℝ} (hb : 0<b) (hbc : b < c)
--       (he : ThreeExterior g b) {m : ℕ} (hm : 1 ≤ m) (u : ThreeManifold → ℝ)
--       (hu : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius (4*m+1) q) :
--       ∃ x, (chartAt ThreeModel threeProfileCenter).symm x∈threeCollar b c ∧
--         Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
--           coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace`, `OAI.YauCounterexamples.threeIsManifold` and `OAI.YauCounterexamples.threeProfileCenter` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.ThreeExterior` and `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeCollar` and `OAI.YauCounterexamples.threeCoupled` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.three_pin_near` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean (declaration OAI.YauCounterexamples.three_collar_rank)

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
lemma three_collar_rank
    (g : SmoothMetric ThreeModel ThreeManifold) {b c : ℝ} (hb : 0<b) (hbc : b < c)
    (he : ThreeExterior g b) {m : ℕ} (hm : 1 ≤ m) (u : ThreeManifold → ℝ)
    (hu : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius (4*m+1) q) :
    ∃ x, (chartAt ThreeModel threeProfileCenter).symm x∈threeCollar b c ∧
      Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x) := by
  sorry

end

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end
