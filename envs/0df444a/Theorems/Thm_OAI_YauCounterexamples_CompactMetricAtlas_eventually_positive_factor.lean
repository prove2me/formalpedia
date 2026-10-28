-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_eventually_positive_factor
-- name    : OAI.YauCounterexamples.CompactMetricAtlas.eventually_positive_factor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:51:59.082981+00:00
-- url     : https://prove2.me/theorems/cd8b8d21-ea95-4722-a29a-69e4487857de
-- title:
--   OAI.YauCounterexamples.CompactMetricAtlas.eventually_positive_factor: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.CompactMetricAtlas.eventually_positive_factor` of [lean/OAI/Geometry/SmoothYau/Limits/CubicConstantNonneg.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CubicConstantNonneg.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples.CompactMetricAtlas`, with `open Set Filter Function`, `open scoped Topology ContDiff Manifold SchwartzMap`, `open Set Filter Manifold Bundle MeasureTheory NNReal`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Topology NNReal`, `open Set Filter Module`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`, `open Set Filter`, `open scoped Topology`, `open Set Filter Function MeasureTheory FourierTransform TemperedDistribution`, `open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction`, `open Filter`, `open scoped Topology ContDiff Manifold`):
--
--   ```lean
--   theorem eventually_positive_factor
--       (hd : Module.finrank ℝ E = 3) (B : ∀ i, A.PatchCoefficients i)
--       (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)))
--       (b s : ℕ → M → ℝ)
--       (hb : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (b n))
--       (hsmooth : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (s n))
--       (Λ ε δ : ℕ → ℝ)
--       (hΛ : Tendsto Λ atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
--       (hδ : Tendsto δ atTop (𝓝 0))
--       (hΛε : Tendsto (fun n => Λ n * ε n) atTop (𝓝 0))
--       (hΛδ : Tendsto (fun n => Λ n * δ n) atTop (𝓝 0))
--       (hstart : Tendsto (fun n => Λ n * ε n / δ n) atTop (𝓝 0))
--       (hpos : ∀ᶠ n in atTop, 0 ≤ ε n ∧ 0 < δ n)
--       (hdata : ∀ᶠ n in atTop,
--         ‖A.realOfSmooth _ ht (fun x => b n x - 1) ((hb n).sub contMDiff_const)‖ ≤ ε n ∧
--         ‖A.realOfSmooth _ ht (fun x => s n x - 1) ((hsmooth n).sub contMDiff_const)‖ ≤ ε n) :
--       ∀ᶠ n in atTop, ∃ u : M → ℝ,
--         ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u ∧ (∀ x, 0 < u x) ∧
--         (∀ x, weightedLaplacian g (b n) u x =
--           Λ n * b n x ^ 3 * u x ^ 5 - Λ n * s n x * u x) ∧
--         ∃ h : A.realH (2 * ((k + 1 : ℕ) : ℝ)), ‖h‖ ≤ δ n ∧
--           ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) h x = u x - 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CompactMetricAtlas`, `OAI.YauCounterexamples.FourierSobolevSpace`, `OAI.YauCounterexamples.CompactMetricAtlas.H` and `OAI.YauCounterexamples.CompactMetricAtlas.PatchCoefficients` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.weightedLaplacian` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.CompactMetricAtlas.realH`, `OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg` and `OAI.YauCounterexamples.CompactMetricAtlas.realValue` (definitions bundle `OAIQ070A005` of this split); `OAI.YauCounterexamples.CompactMetricAtlas.realOfSmooth` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_factor_raw` and `OAI.YauCounterexamples.exists_three_scalar_producer` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CubicConstantNonneg.lean (declaration OAI.YauCounterexamples.CompactMetricAtlas.eventually_positive_factor)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009

section

attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
namespace YauCounterexamples
open Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem eventually_positive_factor
    (hd : Module.finrank ℝ E = 3) (B : ∀ i, A.PatchCoefficients i)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)))
    (b s : ℕ → M → ℝ)
    (hb : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (b n))
    (hsmooth : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (s n))
    (Λ ε δ : ℕ → ℝ)
    (hΛ : Tendsto Λ atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hΛε : Tendsto (fun n => Λ n * ε n) atTop (𝓝 0))
    (hΛδ : Tendsto (fun n => Λ n * δ n) atTop (𝓝 0))
    (hstart : Tendsto (fun n => Λ n * ε n / δ n) atTop (𝓝 0))
    (hpos : ∀ᶠ n in atTop, 0 ≤ ε n ∧ 0 < δ n)
    (hdata : ∀ᶠ n in atTop,
      ‖A.realOfSmooth _ ht (fun x => b n x - 1) ((hb n).sub contMDiff_const)‖ ≤ ε n ∧
      ‖A.realOfSmooth _ ht (fun x => s n x - 1) ((hsmooth n).sub contMDiff_const)‖ ≤ ε n) :
    ∀ᶠ n in atTop, ∃ u : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u ∧ (∀ x, 0 < u x) ∧
      (∀ x, weightedLaplacian g (b n) u x =
        Λ n * b n x ^ 3 * u x ^ 5 - Λ n * s n x * u x) ∧
      ∃ h : A.realH (2 * ((k + 1 : ℕ) : ℝ)), ‖h‖ ≤ δ n ∧
        ∀ x, A.realValue (2 * ((k + 1 : ℕ) : ℝ)) h x = u x - 1 := by
  sorry
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end
