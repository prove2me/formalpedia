-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_three_simple_pinned_family
-- name    : OAI.YauCounterexamples.exists_three_simple_pinned_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:44:47.071997+00:00
-- url     : https://prove2.me/theorems/e842d3c0-ea59-47df-8295-617bb4e53ba7
-- title:
--   OAI.YauCounterexamples.exists_three_simple_pinned_family: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_three_simple_pinned_family` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   theorem exists_three_simple_pinned_family
--       (I : MetricIntegralAtlas (E := ThreeModel) (M := ThreeManifold))
--       (g : SmoothMetric ThreeModel ThreeManifold)
--       {Λ : ℝ} (hΛ : 0<Λ) {S : Set ThreeManifold} (hS : IsOpen S)
--       (u : RealSmoothFunctions ThreeModel ThreeManifold)
--       (hu0 : (u : ThreeManifold → ℝ) ≠ 0)
--       (hue : ∀ p, -laplaceBeltrami g u p = Λ*u p)
--       (hG : ∀ p∈S, 0 < coordinateGradientPair g u u p)
--       (hrank : ∃ x, (chartAt ThreeModel threeProfileCenter).symm x∈S ∧
--         Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
--           coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x))
--       : ∃ K : pinningTensorSpace g (u : ThreeManifold → ℝ)
--         S,
--         ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ v : ThreeManifold → ℝ,
--           ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v →
--           (∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) v x =
--             Λ*v x) → ∃ c : ℝ, v = fun x => c*u x
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.MetricIntegralAtlas` (definitions bundle `OAIQ070A001` of this split); `OAI.YauCounterexamples.RealSmoothFunctions` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.metricGradient`, `OAI.YauCounterexamples.threeChartedSpace`, `OAI.YauCounterexamples.threeIsManifold` and `OAI.YauCounterexamples.threeProfileCenter` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.pinnedMetric` and `OAI.YauCounterexamples.pinningTensorSpace` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.three_pin_near` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean (declaration OAI.YauCounterexamples.exists_three_simple_pinned_family)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem exists_three_simple_pinned_family
    (I : MetricIntegralAtlas (E := ThreeModel) (M := ThreeManifold))
    (g : SmoothMetric ThreeModel ThreeManifold)
    {Λ : ℝ} (hΛ : 0<Λ) {S : Set ThreeManifold} (hS : IsOpen S)
    (u : RealSmoothFunctions ThreeModel ThreeManifold)
    (hu0 : (u : ThreeManifold → ℝ) ≠ 0)
    (hue : ∀ p, -laplaceBeltrami g u p = Λ*u p)
    (hG : ∀ p∈S, 0 < coordinateGradientPair g u u p)
    (hrank : ∃ x, (chartAt ThreeModel threeProfileCenter).symm x∈S ∧
      Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x))
    : ∃ K : pinningTensorSpace g (u : ThreeManifold → ℝ)
      S,
      ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ v : ThreeManifold → ℝ,
        ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v →
        (∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) v x =
          Λ*v x) → ∃ c : ℝ, v = fun x => c*u x := by
  sorry
end

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end
