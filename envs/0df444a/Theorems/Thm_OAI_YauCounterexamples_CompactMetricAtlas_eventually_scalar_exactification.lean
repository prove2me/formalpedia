-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_eventually_scalar_exactification
-- name    : OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_exactification
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:31:35.295607+00:00
-- url     : https://prove2.me/theorems/421e6930-5bb2-4788-8059-d2cd4804adc6
-- title:
--   OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_exactification: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_exactification` of [lean/OAI/Geometry/SmoothYau/Estimates/EventualProductScalarCorrectionRate.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/EventualProductScalarCorrectionRate.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples.CompactMetricAtlas`, with `open Set Filter Function`, `open scoped Topology ContDiff Manifold SchwartzMap`, `open Set Filter Manifold Bundle MeasureTheory NNReal`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Topology NNReal`, `open Set Filter Module`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold Matrix`, `open Set Filter`, `open scoped Topology`, `open Set Filter Function MeasureTheory FourierTransform TemperedDistribution`, `open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction`, `open Set Filter Function`, `open scoped Topology ContDiff Manifold`, `open Filter`, `open scoped Topology ContDiff Manifold`):
--
--   ```lean
--   theorem eventually_scalar_exactification
--       (h B P D : ℕ) (hP : 0 < P) (hD : P+((2*B+21)*(h+2)+10)+2 ≤ D)
--       {C : ℝ} (hC : 0 < C) (U W : ℕ → M → ℝ)
--       (hU : ∀ n, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (U n))
--       (hW : ∀ n x, 0 < W n x)
--       (hdata : ∀ᶠ n : ℕ in atTop,
--         (∀ x, W n x/(n:ℝ)^B ≤ |U n x|+
--           Real.sqrt (coordinateGradientPair g (U n) (U n) x)/(n:ℝ)) ∧
--         (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ h+2,
--           ‖iteratedFDeriv ℝ j (U n ∘ (chartAt E (A.p i)).symm) y‖ ≤
--             C*(n:ℝ)^(j+4)*W n ((chartAt E (A.p i)).symm y)) ∧
--         (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ h+1,
--           ‖iteratedFDeriv ℝ j
--             ((fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x) ∘
--               (chartAt E (A.p i)).symm) y‖ ≤
--             C*(n:ℝ)^4/(n:ℝ)^D*W n ((chartAt E (A.p i)).symm y))) :
--       ∀ᶠ n : ℕ in atTop,
--         let b := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n)
--         let s := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) (U n)
--         ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s ∧
--         (∀ x, 0 < b x ∧ 0 < s x) ∧
--         (∀ x, weightedLaplacian g b (U n) x+sphereFrequency n*s x*U n x=0) ∧
--         A.ChartJetBound h (fun x => ((b x-1:ℝ):ℂ)) (inverseFrequency n^P) ∧
--         A.ChartJetBound h (fun x => ((s x-1:ℝ):ℂ)) (inverseFrequency n^P) ∧
--         (∀ x, |b x-1|+|s x-1| ≤ inverseFrequency n^P) ∧
--         (tsupport (fun x => b x-1) ⊆
--           tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) ∧
--         (tsupport (fun x => s x-1) ⊆
--           tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CompactMetricAtlas`, `OAI.YauCounterexamples.CompactMetricAtlas.ChartJetBound`, `OAI.YauCounterexamples.CompactMetricAtlas.p` and `OAI.YauCounterexamples.CompactMetricAtlas.scalarChartSupport` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.coordinateGradientPair`, `OAI.YauCounterexamples.inverseFrequency`, `OAI.YauCounterexamples.sphereFrequency` and `OAI.YauCounterexamples.weightedLaplacian` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.intrinsicCorrectionB` and `OAI.YauCounterexamples.intrinsicCorrectionS` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_factor_raw` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/EventualProductScalarCorrectionRate.lean (declaration OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_exactification)

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
open Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
theorem eventually_scalar_exactification
    (h B P D : ℕ) (hP : 0 < P) (hD : P+((2*B+21)*(h+2)+10)+2 ≤ D)
    {C : ℝ} (hC : 0 < C) (U W : ℕ → M → ℝ)
    (hU : ∀ n, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (U n))
    (hW : ∀ n x, 0 < W n x)
    (hdata : ∀ᶠ n : ℕ in atTop,
      (∀ x, W n x/(n:ℝ)^B ≤ |U n x|+
        Real.sqrt (coordinateGradientPair g (U n) (U n) x)/(n:ℝ)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ h+2,
        ‖iteratedFDeriv ℝ j (U n ∘ (chartAt E (A.p i)).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*W n ((chartAt E (A.p i)).symm y)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ h+1,
        ‖iteratedFDeriv ℝ j
          ((fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x) ∘
            (chartAt E (A.p i)).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*W n ((chartAt E (A.p i)).symm y))) :
    ∀ᶠ n : ℕ in atTop,
      let b := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n)
      let s := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) (U n)
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s ∧
      (∀ x, 0 < b x ∧ 0 < s x) ∧
      (∀ x, weightedLaplacian g b (U n) x+sphereFrequency n*s x*U n x=0) ∧
      A.ChartJetBound h (fun x => ((b x-1:ℝ):ℂ)) (inverseFrequency n^P) ∧
      A.ChartJetBound h (fun x => ((s x-1:ℝ):ℂ)) (inverseFrequency n^P) ∧
      (∀ x, |b x-1|+|s x-1| ≤ inverseFrequency n^P) ∧
      (tsupport (fun x => b x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) ∧
      (tsupport (fun x => s x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) := by
  sorry
end CompactMetricAtlas

end

open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end
