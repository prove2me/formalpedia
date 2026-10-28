-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_three_robust_global_profile_family
-- name    : OAI.YauCounterexamples.exists_three_robust_global_profile_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:07:53.493261+00:00
-- url     : https://prove2.me/theorems/05fb5156-09ab-4fda-89c2-7baa4a9f5bef
-- title:
--   OAI.YauCounterexamples.exists_three_robust_global_profile_family: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_three_robust_global_profile_family` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeRobustProfileNormedSpace.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeRobustProfileNormedSpace.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric MeasureTheory BoxIntegral`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   theorem exists_three_robust_global_profile_family :
--       ∃ C R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
--         IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
--         ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
--         ∃ δ>0, ∃ I : Box (Fin 3),
--           normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
--           ∀ T : ℝ, ∃ Φ : ThreeManifold → ℝ,
--             ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ Φ ∧
--             ContDiff ℝ ∞ (Φ ∘ threeNormalInv) ∧
--             tsupport (fun p => Φ p-C) ⊆ threeNormalInv '' closedBall 0 (3*R/4) ∧
--             (∀ y ∈ closedBall 0 b,
--               coordinateMetricGradient (threeNormalMetricOf g) (Φ ∘ threeNormalInv) y ≠ 0 ∧
--               actualProfileStrict (threeNormalMetricOf g) (Φ ∘ threeNormalInv) y) ∧
--             (∀ y ∈ closedBall 0 a,
--               threeGlobalLog (threeNormalInv y)+δ/2 < Φ (threeNormalInv y)) ∧
--             (∀ p ∉ threeNormalInv '' closedBall 0 b, Φ p≤threeGlobalLog p-δ) ∧
--             T < ∫ x in Box.Icc I, profileFrequencyScale (threeNormalMetricOf g)
--               (Φ ∘ threeNormalInv) (normalWaveEquiv x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.ThreeCleanBall`, `OAI.YauCounterexamples.coordinateMetricGradient`, `OAI.YauCounterexamples.threeBackgroundMetric` and `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeRobustProfileNormedSpace` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.actualProfileStrict` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.profileFrequencyScale`, `OAI.YauCounterexamples.threeGlobalLog` and `OAI.YauCounterexamples.threeNormalMetricOf` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsSmoothNeighborhood`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_chart_quasimodes_with_gaps` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeRobustProfileNormedSpace.lean (declaration OAI.YauCounterexamples.exists_three_robust_global_profile_family)

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

open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

attribute [local instance] OAI.YauCounterexamples.threeRobustProfileNormedSpace
local instance threeRobustProfileContinuousSMul_rb510ca_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
theorem exists_three_robust_global_profile_family :
    ∃ C R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
      ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∃ δ>0, ∃ I : Box (Fin 3),
        normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
        ∀ T : ℝ, ∃ Φ : ThreeManifold → ℝ,
          ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ Φ ∧
          ContDiff ℝ ∞ (Φ ∘ threeNormalInv) ∧
          tsupport (fun p => Φ p-C) ⊆ threeNormalInv '' closedBall 0 (3*R/4) ∧
          (∀ y ∈ closedBall 0 b,
            coordinateMetricGradient (threeNormalMetricOf g) (Φ ∘ threeNormalInv) y ≠ 0 ∧
            actualProfileStrict (threeNormalMetricOf g) (Φ ∘ threeNormalInv) y) ∧
          (∀ y ∈ closedBall 0 a,
            threeGlobalLog (threeNormalInv y)+δ/2 < Φ (threeNormalInv y)) ∧
          (∀ p ∉ threeNormalInv '' closedBall 0 b, Φ p≤threeGlobalLog p-δ) ∧
          T < ∫ x in Box.Icc I, profileFrequencyScale (threeNormalMetricOf g)
            (Φ ∘ threeNormalInv) (normalWaveEquiv x) := by
  sorry

end YauCounterexamples
end

end OAI
end
