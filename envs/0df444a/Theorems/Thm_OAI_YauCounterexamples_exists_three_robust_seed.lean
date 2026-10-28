-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_three_robust_seed
-- name    : OAI.YauCounterexamples.exists_three_robust_seed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:08:18.520782+00:00
-- url     : https://prove2.me/theorems/645ba519-9a04-4f4e-87d3-6510ed1fd7f5
-- title:
--   OAI.YauCounterexamples.exists_three_robust_seed: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_three_robust_seed` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeRobustProfileNormedSpace.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeRobustProfileNormedSpace.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric MeasureTheory BoxIntegral`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   theorem exists_three_robust_seed :
--       ∃ C R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ F : NormalWaveSpace → ℝ,
--         ContDiff ℝ ∞ F ∧ (∀ y ∈ closedBall 0 R, F y=threeGlobalLog (threeNormalInv y)) ∧
--         (∀ p, C+1≤threeGlobalLog p) ∧
--         ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
--           IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
--           ∀ g ∈ N, ∀ y ∈ closedBall 0 R,
--             coordinateMetricGradient (threeNormalMetricOf g) F y ≠ 0 ∧
--             actualProfileStrict (threeNormalMetricOf g) F y
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.ThreeCleanBall`, `OAI.YauCounterexamples.coordinateMetricGradient`, `OAI.YauCounterexamples.threeBackgroundMetric` and `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeRobustNormedSpace` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.actualProfileStrict` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.threeGlobalLog` and `OAI.YauCounterexamples.threeNormalMetricOf` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsSmoothNeighborhood`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_robust_exhaustible_envelopes` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeRobustProfileNormedSpace.lean (declaration OAI.YauCounterexamples.exists_three_robust_seed)

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
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

attribute [local instance] OAI.YauCounterexamples.threeRobustNormedSpace
local instance threeRobustContinuousSMul_r85332b_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
theorem exists_three_robust_seed :
    ∃ C R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ F : NormalWaveSpace → ℝ,
      ContDiff ℝ ∞ F ∧ (∀ y ∈ closedBall 0 R, F y=threeGlobalLog (threeNormalInv y)) ∧
      (∀ p, C+1≤threeGlobalLog p) ∧
      ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
        IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
        ∀ g ∈ N, ∀ y ∈ closedBall 0 R,
          coordinateMetricGradient (threeNormalMetricOf g) F y ≠ 0 ∧
          actualProfileStrict (threeNormalMetricOf g) F y := by
  sorry

end

open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end
