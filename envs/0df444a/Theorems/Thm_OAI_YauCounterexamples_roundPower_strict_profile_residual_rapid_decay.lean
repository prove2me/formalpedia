-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_roundPower_strict_profile_residual_rapid_decay
-- name    : OAI.YauCounterexamples.roundPower_strict_profile_residual_rapid_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:46:40.412733+00:00
-- url     : https://prove2.me/theorems/552091b4-84bc-4206-a62a-00fefdfc71f4
-- title:
--   OAI.YauCounterexamples.roundPower_strict_profile_residual_rapid_decay: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.roundPower_strict_profile_residual_rapid_decay` of [lean/OAI/Geometry/SmoothYau/Geometry/RoundPowerGlobalProfileResidual.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/RoundPowerGlobalProfileResidual.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function`, `open scoped Topology ContDiff Manifold SchwartzMap`, `open Set Filter Manifold Bundle MeasureTheory NNReal`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Topology NNReal`, `open Set Filter Module`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`, `open Set Filter`, `open scoped Topology`, `open Set Filter Function MeasureTheory FourierTransform TemperedDistribution`, `open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold`, `open Set Filter Manifold Bundle Matrix`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold InnerProductSpace`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold InnerProductSpace`):
--
--   ```lean
--   theorem roundPower_strict_profile_residual_rapid_decay
--       (g : SmoothMetric (Euclidean 3) (Sphere 3))
--       (a b : Euclidean (3+1)) (p : Sphere 3) {K : Set (Euclidean 3)}
--       (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean 3) p).target)
--       (φ : Euclidean 3 → ℝ) (hφ : ContinuousOn φ K) (h P : ℕ)
--       (hgap : ∀ y ∈ K, roundPlanarChart a b p y ≠ 0 →
--         Real.log ‖roundPlanarChart a b p y‖ < φ y) :
--       ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ y ∈ K, ∀ j ≤ h,
--         ‖iteratedFDeriv ℝ j
--           ((fun z => laplaceBeltrami g (roundPower a b n) z +
--             (n:ℝ)*((n:ℝ)+2)*roundPower a b n z) ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤
--           ((n:ℝ)^P)⁻¹*Real.exp ((n:ℝ)*φ y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.roundPlanarChart` and `OAI.YauCounterexamples.roundPower` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.roundPower_global_profile_residual_rapid_decay` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/RoundPowerGlobalProfileResidual.lean (declaration OAI.YauCounterexamples.roundPower_strict_profile_residual_rapid_decay)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace

theorem roundPower_strict_profile_residual_rapid_decay
    (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (a b : Euclidean (3+1)) (p : Sphere 3) {K : Set (Euclidean 3)}
    (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean 3) p).target)
    (φ : Euclidean 3 → ℝ) (hφ : ContinuousOn φ K) (h P : ℕ)
    (hgap : ∀ y ∈ K, roundPlanarChart a b p y ≠ 0 →
      Real.log ‖roundPlanarChart a b p y‖ < φ y) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j
        ((fun z => laplaceBeltrami g (roundPower a b n) z +
          (n:ℝ)*((n:ℝ)+2)*roundPower a b n z) ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤
        ((n:ℝ)^P)⁻¹*Real.exp ((n:ℝ)*φ y) := by
  sorry

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace

end YauCounterexamples
end

end OAI
end
