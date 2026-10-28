-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_three_rank_separating_tensor
-- name    : OAI.YauCounterexamples.three_rank_separating_tensor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:49:20.320507+00:00
-- url     : https://prove2.me/theorems/03cb9b6a-d021-4d22-9c54-1ca3eef557b9
-- title:
--   OAI.YauCounterexamples.three_rank_separating_tensor: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.three_rank_separating_tensor` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle MeasureTheory Metric`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   lemma three_rank_separating_tensor
--       (μ : Measure ThreeManifold) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
--       (g : SmoothMetric ThreeModel ThreeManifold) {u v : ThreeManifold → ℝ}
--       (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u)
--       (hv : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v)
--       {Λ : ℝ} (hΛ : 0<Λ) (hue : ∀ p, -laplaceBeltrami g u p=Λ*u p)
--       (hve : ∀ p, -laplaceBeltrami g v p=Λ*v p)
--       {S : Set ThreeManifold} (hS : IsOpen S)
--       (hG : ∀ p∈S, 0 < coordinateGradientPair g u u p)
--       (hrank : ∃ x : ThreeModel, (chartAt ThreeModel threeProfileCenter).symm x∈S ∧
--         Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
--           coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x))
--       (hv0 : v≠0) (ho : ∫ x, v x*u x ∂μ=0) :
--       ∃ χ : ThreeManifold → ℝ, tsupport χ⊆S ∧
--         ContMDiff 𝓘(ℝ,ThreeModel) (𝓘(ℝ,ThreeModel).prod 𝓘(ℝ,ThreeModel →L[ℝ] ThreeModel)) ∞
--           (fun y => TotalSpace.mk' (ThreeModel →L[ℝ] ThreeModel) y (supportedPinningTensor g u v χ y)) ∧
--         (∀ y, LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,ThreeModel) y)
--           (supportedPinningTensor g u v χ y).toLinearMap=0) ∧
--         (∀ y, supportedPinningTensor g u v χ y (metricGradient g u y)=0) ∧
--         0<∫ y, g.inner y (metricGradient g v y)
--           (supportedPinningTensor g u v χ y (metricGradient g v y)) ∂μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.metricGradient`, `OAI.YauCounterexamples.threeChartedSpace`, `OAI.YauCounterexamples.threeIsManifold` and `OAI.YauCounterexamples.threeProfileCenter` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.instMeasurableSpaceThreeManifold` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.supportedPinningTensor` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.three_nondegenerate_pinning_tensor` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeFixedFormNorm.lean (declaration OAI.YauCounterexamples.three_rank_separating_tensor)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007
import Definitions.Def_OAIQ070A008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
attribute [local instance] OAI.YauCounterexamples.instMeasurableSpaceThreeManifold
local instance instBorelSpaceThreeManifold_r781031_1 : BorelSpace ThreeManifold := ⟨rfl⟩
lemma three_rank_separating_tensor
    (μ : Measure ThreeManifold) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (g : SmoothMetric ThreeModel ThreeManifold) {u v : ThreeManifold → ℝ}
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v)
    {Λ : ℝ} (hΛ : 0<Λ) (hue : ∀ p, -laplaceBeltrami g u p=Λ*u p)
    (hve : ∀ p, -laplaceBeltrami g v p=Λ*v p)
    {S : Set ThreeManifold} (hS : IsOpen S)
    (hG : ∀ p∈S, 0 < coordinateGradientPair g u u p)
    (hrank : ∃ x : ThreeModel, (chartAt ThreeModel threeProfileCenter).symm x∈S ∧
      Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x))
    (hv0 : v≠0) (ho : ∫ x, v x*u x ∂μ=0) :
    ∃ χ : ThreeManifold → ℝ, tsupport χ⊆S ∧
      ContMDiff 𝓘(ℝ,ThreeModel) (𝓘(ℝ,ThreeModel).prod 𝓘(ℝ,ThreeModel →L[ℝ] ThreeModel)) ∞
        (fun y => TotalSpace.mk' (ThreeModel →L[ℝ] ThreeModel) y (supportedPinningTensor g u v χ y)) ∧
      (∀ y, LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,ThreeModel) y)
        (supportedPinningTensor g u v χ y).toLinearMap=0) ∧
      (∀ y, supportedPinningTensor g u v χ y (metricGradient g u y)=0) ∧
      0<∫ y, g.inner y (metricGradient g v y)
        (supportedPinningTensor g u v χ y (metricGradient g v y)) ∂μ := by
  sorry
end

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end
