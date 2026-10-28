-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_three_nondegenerate_pinning_tensor
-- name    : OAI.YauCounterexamples.three_nondegenerate_pinning_tensor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:16:33.701711+00:00
-- url     : https://prove2.me/theorems/c25fdf8c-66b8-45ec-a9a8-3ac00fd5352c
-- title:
--   OAI.YauCounterexamples.three_nondegenerate_pinning_tensor: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.three_nondegenerate_pinning_tensor` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   theorem three_nondegenerate_pinning_tensor
--       (I : MetricIntegralAtlas (E := ThreeModel) (M := ThreeManifold))
--       (g : SmoothMetric ThreeModel ThreeManifold)
--       {Λ : ℝ} (hΛ : 0<Λ) {S : Set ThreeManifold} (hS : IsOpen S)
--       (u : RealSmoothFunctions ThreeModel ThreeManifold)
--       (hue : ∀ p, -laplaceBeltrami g u p = Λ*u p)
--       (hG : ∀ p∈S, 0 < coordinateGradientPair g u u p)
--       (hrank : ∃ x, (chartAt ThreeModel threeProfileCenter).symm x∈S ∧
--         Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
--           coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x))
--       (σ : W →ₗ[ℝ] RealSmoothFunctions ThreeModel ThreeManifold)
--       (hσ : Injective σ)
--       (hσe : ∀ w p, -laplaceBeltrami g (σ w) p = Λ*σ w p)
--       (hσo : ∀ w, I.mean g (fun x => σ w x*u x) = 0) :
--       ∃ K : pinningTensorSpace g (u : ThreeManifold → ℝ)
--         S,
--         (restrictedPinningPencil I g σ K).Nondegenerate
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.MetricIntegralAtlas` (definitions bundle `OAIQ070A001` of this split); `OAI.YauCounterexamples.RealSmoothFunctions` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace`, `OAI.YauCounterexamples.threeIsManifold` and `OAI.YauCounterexamples.threeProfileCenter` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.MetricIntegralAtlas.mean` (definitions bundle `OAIQ070A005` of this split); `OAI.YauCounterexamples.pinningTensorSpace` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.restrictedPinningPencil` (definitions bundle `OAIQ070A011` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_simple_pinned_family` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean (declaration OAI.YauCounterexamples.three_nondegenerate_pinning_tensor)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A011

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

theorem three_nondegenerate_pinning_tensor
    (I : MetricIntegralAtlas (E := ThreeModel) (M := ThreeManifold))
    (g : SmoothMetric ThreeModel ThreeManifold)
    {Λ : ℝ} (hΛ : 0<Λ) {S : Set ThreeManifold} (hS : IsOpen S)
    (u : RealSmoothFunctions ThreeModel ThreeManifold)
    (hue : ∀ p, -laplaceBeltrami g u p = Λ*u p)
    (hG : ∀ p∈S, 0 < coordinateGradientPair g u u p)
    (hrank : ∃ x, (chartAt ThreeModel threeProfileCenter).symm x∈S ∧
      Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x))
    (σ : W →ₗ[ℝ] RealSmoothFunctions ThreeModel ThreeManifold)
    (hσ : Injective σ)
    (hσe : ∀ w p, -laplaceBeltrami g (σ w) p = Λ*σ w p)
    (hσo : ∀ w, I.mean g (fun x => σ w x*u x) = 0) :
    ∃ K : pinningTensorSpace g (u : ThreeManifold → ℝ)
      S,
      (restrictedPinningPencil I g σ K).Nondegenerate := by
  sorry

end

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end
