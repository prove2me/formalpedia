-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_supported_separating_tensor
-- name    : OAI.YauCounterexamples.exists_supported_separating_tensor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:43:04.551648+00:00
-- url     : https://prove2.me/theorems/a67ad7c3-a916-48e6-ab0a-1b99d033a5b1
-- title:
--   OAI.YauCounterexamples.exists_supported_separating_tensor: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_supported_separating_tensor` of [lean/OAI/Geometry/SmoothYau/Smoothness/ExistsSupportedPinningBump.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ExistsSupportedPinningBump.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem exists_supported_separating_tensor [MeasurableSpace M] [OpensMeasurableSpace M]
--       (μ : Measure M) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
--       (g : SmoothMetric E M) {u v : M → ℝ}
--       (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
--       (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) {A : Set M}
--       (hA : IsOpen A) (hn : ∀ x ∈ A, metricGradient g u x ≠ 0)
--       {x : M} (hx : x ∈ A) (hp : bundleTransverse g u x (metricGradient g v x) ≠ 0)
--       (hd : Module.finrank ℝ E = 3) :
--       ∃ χ : M → ℝ, tsupport χ ⊆ A ∧
--         ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
--           (fun y => TotalSpace.mk' (E →L[ℝ] E) y (supportedPinningTensor g u v χ y)) ∧
--         (∀ y, LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,E) y)
--           (supportedPinningTensor g u v χ y).toLinearMap = 0) ∧
--         (∀ y, supportedPinningTensor g u v χ y (metricGradient g u y) = 0) ∧
--         0 < ∫ y, g.inner y (metricGradient g v y)
--           (supportedPinningTensor g u v χ y (metricGradient g v y)) ∂μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.bundleTransverse` and `OAI.YauCounterexamples.metricGradient` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.supportedPinningTensor` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.annular_eigenfunction_separating_tensor`, `OAI_YauCounterexamples_annular_nondegenerate_pinning_tensor` and `OAI.YauCounterexamples.three_rank_separating_tensor` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ExistsSupportedPinningBump.lean (declaration OAI.YauCounterexamples.exists_supported_separating_tensor)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A008

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_supported_separating_tensor [MeasurableSpace M] [OpensMeasurableSpace M]
    (μ : Measure M) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (g : SmoothMetric E M) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) {A : Set M}
    (hA : IsOpen A) (hn : ∀ x ∈ A, metricGradient g u x ≠ 0)
    {x : M} (hx : x ∈ A) (hp : bundleTransverse g u x (metricGradient g v x) ≠ 0)
    (hd : Module.finrank ℝ E = 3) :
    ∃ χ : M → ℝ, tsupport χ ⊆ A ∧
      ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
        (fun y => TotalSpace.mk' (E →L[ℝ] E) y (supportedPinningTensor g u v χ y)) ∧
      (∀ y, LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,E) y)
        (supportedPinningTensor g u v χ y).toLinearMap = 0) ∧
      (∀ y, supportedPinningTensor g u v χ y (metricGradient g u y) = 0) ∧
      0 < ∫ y, g.inner y (metricGradient g v y)
        (supportedPinningTensor g u v χ y (metricGradient g v y)) ∂μ := by
  sorry
end YauCounterexamples

end

end OAI
end
