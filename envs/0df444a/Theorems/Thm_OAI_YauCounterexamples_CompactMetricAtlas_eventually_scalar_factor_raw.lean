-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_eventually_scalar_factor_raw
-- name    : OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_factor_raw
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:32:09.402015+00:00
-- url     : https://prove2.me/theorems/5e39c188-99c9-4013-bbb6-a136a689d73f
-- title:
--   OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_factor_raw: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_factor_raw` of [lean/OAI/Geometry/SmoothYau/Estimates/ExistsSphericalScalarProducer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/ExistsSphericalScalarProducer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples.CompactMetricAtlas`, with `open Set Filter Function Manifold`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem eventually_scalar_factor_raw
--       (hd : Module.finrank ℝ E=3) (tests : List (CoordinateTest E M))
--       (N P B D : ℕ) (hNP : N ≤ 2*(k+1))
--       (hN : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ)-N))
--       (hD : (P+8)+((2*B+21)*(2*(k+1)+2)+10)+2 ≤ D)
--       {C : ℝ} (hC : 0 < C) (U W : ℕ → M → ℝ)
--       (hU : ∀ n, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (U n))
--       (hW : ∀ n x, 0 < W n x)
--       (hdata : ∀ᶠ n : ℕ in atTop,
--         (∀ x, W n x/(n:ℝ)^B ≤ |U n x|+
--           Real.sqrt (coordinateGradientPair g (U n) (U n) x)/(n:ℝ)) ∧
--         (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ 2*(k+1)+2,
--           ‖iteratedFDeriv ℝ j (U n ∘ (chartAt E (A.p i)).symm) y‖ ≤
--             C*(n:ℝ)^(j+4)*W n ((chartAt E (A.p i)).symm y)) ∧
--         (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ 2*(k+1)+1,
--           ‖iteratedFDeriv ℝ j
--             ((fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x) ∘
--               (chartAt E (A.p i)).symm) y‖ ≤
--             C*(n:ℝ)^4/(n:ℝ)^D*W n ((chartAt E (A.p i)).symm y))) :
--       ∃ L > 0, ∀ᶠ n : ℕ in atTop,
--         let b := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n)
--         let s := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) (U n)
--         ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s ∧
--         (∀ x, 0 < b x ∧ 0 < s x) ∧
--         (∀ x, weightedLaplacian g b (U n) x+sphereFrequency n*s x*U n x=0) ∧
--         (tsupport (fun x => b x-1) ⊆
--           tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) ∧
--         (tsupport (fun x => s x-1) ⊆
--           tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) ∧
--         ∃ v : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
--           (∀ x, weightedLaplacian g b v x =
--             sphereFrequency n*b x^3*v x^5-sphereFrequency n*s x*v x) ∧
--           (∀ x, |b x-1| ≤ L*inverseFrequency n^P ∧
--             |s x-1| ≤ L*inverseFrequency n^P ∧ |v x-1| ≤ L*inverseFrequency n^P) ∧
--           (∀ t ∈ tests, ∀ y ∈ t.compactSet, ∀ j ≤ N,
--             ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
--             ‖iteratedFDeriv ℝ j ((fun x => s x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
--             ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CompactMetricAtlas`, `OAI.YauCounterexamples.CompactMetricAtlas.p` and `OAI.YauCounterexamples.CompactMetricAtlas.scalarChartSupport` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.coordinateGradientPair`, `OAI.YauCounterexamples.inverseFrequency`, `OAI.YauCounterexamples.sphereFrequency` and `OAI.YauCounterexamples.weightedLaplacian` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.intrinsicCorrectionB` and `OAI.YauCounterexamples.intrinsicCorrectionS` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.CoordinateTest`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_scalar_producer` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/ExistsSphericalScalarProducer.lean (declaration OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_factor_raw)

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
open Set Filter Function Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)

theorem eventually_scalar_factor_raw
    (hd : Module.finrank ℝ E=3) (tests : List (CoordinateTest E M))
    (N P B D : ℕ) (hNP : N ≤ 2*(k+1))
    (hN : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ)-N))
    (hD : (P+8)+((2*B+21)*(2*(k+1)+2)+10)+2 ≤ D)
    {C : ℝ} (hC : 0 < C) (U W : ℕ → M → ℝ)
    (hU : ∀ n, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (U n))
    (hW : ∀ n x, 0 < W n x)
    (hdata : ∀ᶠ n : ℕ in atTop,
      (∀ x, W n x/(n:ℝ)^B ≤ |U n x|+
        Real.sqrt (coordinateGradientPair g (U n) (U n) x)/(n:ℝ)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ 2*(k+1)+2,
        ‖iteratedFDeriv ℝ j (U n ∘ (chartAt E (A.p i)).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*W n ((chartAt E (A.p i)).symm y)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ 2*(k+1)+1,
        ‖iteratedFDeriv ℝ j
          ((fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x) ∘
            (chartAt E (A.p i)).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*W n ((chartAt E (A.p i)).symm y))) :
    ∃ L > 0, ∀ᶠ n : ℕ in atTop,
      let b := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n)
      let s := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) (U n)
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s ∧
      (∀ x, 0 < b x ∧ 0 < s x) ∧
      (∀ x, weightedLaplacian g b (U n) x+sphereFrequency n*s x*U n x=0) ∧
      (tsupport (fun x => b x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) ∧
      (tsupport (fun x => s x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) ∧
      ∃ v : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
        (∀ x, weightedLaplacian g b v x =
          sphereFrequency n*b x^3*v x^5-sphereFrequency n*s x*v x) ∧
        (∀ x, |b x-1| ≤ L*inverseFrequency n^P ∧
          |s x-1| ≤ L*inverseFrequency n^P ∧ |v x-1| ≤ L*inverseFrequency n^P) ∧
        (∀ t ∈ tests, ∀ y ∈ t.compactSet, ∀ j ≤ N,
          ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => s x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P) := by
  sorry
end CompactMetricAtlas
end YauCounterexamples
end

end OAI
end
