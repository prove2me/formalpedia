-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_spherical_scalar_producer
-- name    : OAI.YauCounterexamples.exists_spherical_scalar_producer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:41:36.715906+00:00
-- url     : https://prove2.me/theorems/e673b69a-c206-4504-bbf9-ca429db42010
-- title:
--   OAI.YauCounterexamples.exists_spherical_scalar_producer: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_spherical_scalar_producer` of [lean/OAI/Geometry/SmoothYau/Estimates/ExistsSphericalScalarProducer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/ExistsSphericalScalarProducer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold Metric MeasureTheory BoxIntegral`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   theorem exists_spherical_scalar_producer
--       (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
--       {t s r : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r) (hr : r < 3/10)
--       {F : Set (Sphere 3)} (hF : IsClosed F)
--       (hFt : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q < t)
--       (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
--         g.inner q v w=g₀.inner q v w)
--       (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
--         ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
--       (A : ℝ) :
--       ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
--         (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
--       ∀ (tests : List (CoordinateTest (Euclidean 3) (Sphere 3))) (N P : ℕ),
--         ∃ L > 0, ∀ᶠ n : ℕ in atTop,
--         ∃ u : Euclidean 3 → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
--           tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
--             ((chartAt (Euclidean 3) sourcePole).symm y) < r} ∧
--         let U := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u
--         let b := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) U
--         let z := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) U
--         (∀ x, U x=0 → 0 < coordinateGradientPair g U U x) ∧
--         ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ b ∧
--         ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ z ∧
--         (∀ x, 0 < b x ∧ 0 < z x) ∧
--         (∀ x, weightedLaplacian g b U x+sphereFrequency n*z x*U x=0) ∧
--         tsupport (fun x => b x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+sphereFrequency n*U x) ∧
--         tsupport (fun x => z x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+sphereFrequency n*U x) ∧
--         ∃ v : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
--           (∀ x, weightedLaplacian g b v x = sphereFrequency n*b x^3*v x^5-sphereFrequency n*z x*v x) ∧
--           (∀ x, |b x-1| ≤ L*inverseFrequency n^P ∧
--             |z x-1| ≤ L*inverseFrequency n^P ∧ |v x-1| ≤ L*inverseFrequency n^P) ∧
--           (∀ a ∈ tests, ∀ y ∈ a.compactSet, ∀ j ≤ N,
--             ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt (Euclidean 3) a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
--             ‖iteratedFDeriv ℝ j ((fun x => z x-1) ∘ (chartAt (Euclidean 3) a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
--             ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt (Euclidean 3) a.center).symm) y‖ ≤ L*inverseFrequency n^P) ∧
--           ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
--             (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
--             (fun a => ε/((n:ℝ)*ℓ a.val))
--             ((U ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.normalWaveEquiv`, `OAI.YauCounterexamples.selfMetricFlat`, `OAI.YauCounterexamples.sourceAxisOne`, `OAI.YauCounterexamples.sourceAxisTwo`, `OAI.YauCounterexamples.sourcePole`, `OAI.YauCounterexamples.sourceSignBox`, `OAI.YauCounterexamples.sphericalCoverage`, `OAI.YauCounterexamples.sphericalRadius` and `OAI.YauCounterexamples.SignTests.signCertificate` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.coordinateGradientPair`, `OAI.YauCounterexamples.inverseFrequency`, `OAI.YauCounterexamples.sphereFrequency` and `OAI.YauCounterexamples.weightedLaplacian` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.sphereChartMetric` and `OAI.YauCounterexamples.sphericalProfileMetricNeighborhood` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.intrinsicCorrectionB`, `OAI.YauCounterexamples.intrinsicCorrectionS`, `OAI.YauCounterexamples.roundPower` and `OAI.YauCounterexamples.sphericalWaveLift` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.CoordinateTest`, `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_exact_stage` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/ExistsSphericalScalarProducer.lean (declaration OAI.YauCounterexamples.exists_spherical_scalar_producer)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples

theorem exists_spherical_scalar_producer
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {t s r : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r) (hr : r < 3/10)
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hFt : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q < t)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    (A : ℝ) :
    ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
      (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
    ∀ (tests : List (CoordinateTest (Euclidean 3) (Sphere 3))) (N P : ℕ),
      ∃ L > 0, ∀ᶠ n : ℕ in atTop,
      ∃ u : Euclidean 3 → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
        tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
          ((chartAt (Euclidean 3) sourcePole).symm y) < r} ∧
      let U := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u
      let b := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) U
      let z := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) U
      (∀ x, U x=0 → 0 < coordinateGradientPair g U U x) ∧
      ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ b ∧
      ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ z ∧
      (∀ x, 0 < b x ∧ 0 < z x) ∧
      (∀ x, weightedLaplacian g b U x+sphereFrequency n*z x*U x=0) ∧
      tsupport (fun x => b x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+sphereFrequency n*U x) ∧
      tsupport (fun x => z x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+sphereFrequency n*U x) ∧
      ∃ v : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
        (∀ x, weightedLaplacian g b v x = sphereFrequency n*b x^3*v x^5-sphereFrequency n*z x*v x) ∧
        (∀ x, |b x-1| ≤ L*inverseFrequency n^P ∧
          |z x-1| ≤ L*inverseFrequency n^P ∧ |v x-1| ≤ L*inverseFrequency n^P) ∧
        (∀ a ∈ tests, ∀ y ∈ a.compactSet, ∀ j ≤ N,
          ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt (Euclidean 3) a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => z x-1) ∘ (chartAt (Euclidean 3) a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt (Euclidean 3) a.center).symm) y‖ ≤ L*inverseFrequency n^P) ∧
        ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
          (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
          (fun a => ε/((n:ℝ)*ℓ a.val))
          ((U ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv) := by
  sorry

end YauCounterexamples
end

end OAI
end
