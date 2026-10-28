-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_three_scalar_producer
-- name    : OAI.YauCounterexamples.exists_three_scalar_producer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:08:29.054321+00:00
-- url     : https://prove2.me/theorems/5f9a1deb-a564-43bc-92f6-4910a264175b
-- title:
--   OAI.YauCounterexamples.exists_three_scalar_producer: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_three_scalar_producer` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold Metric MeasureTheory BoxIntegral`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   theorem exists_three_scalar_producer :
--       ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
--         IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric∈N ∧
--         ∀ g∈N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
--         ∀ F : Set ThreeManifold, IsClosed F → F⊆threeNormalInv '' closedBall 0 a →
--         (∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
--           g.inner q v w=threeBackgroundMetric.inner q v w) → ∀ A : ℝ,
--       ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
--       ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
--         (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
--       ∀ (tests : List (CoordinateTest ThreeModel ThreeManifold)) (N P : ℕ),
--         ∃ L > 0, ∀ᶠ n : ℕ in atTop,
--         ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
--           tsupport u ⊆ ball 0 ((b+R/2)/2) ∧
--         let U := threeCoupled threeCouplingRadius n+threeWaveLift u
--         let b := intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) U
--         let z := intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) U
--         (∀ x, U x=0 → 0 < coordinateGradientPair g U U x) ∧
--         ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ b ∧
--         ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ z ∧
--         (∀ x, 0 < b x ∧ 0 < z x) ∧
--         (∀ x, weightedLaplacian g b U x+productFrequency n*z x*U x=0) ∧
--         tsupport (fun x => b x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+productFrequency n*U x) ∧
--         tsupport (fun x => z x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+productFrequency n*U x) ∧
--         ∃ v : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
--           (∀ x, weightedLaplacian g b v x = productFrequency n*b x^3*v x^5-productFrequency n*z x*v x) ∧
--           (∀ x, |b x-1| ≤ L*inverseFrequency n^P ∧
--             |z x-1| ≤ L*inverseFrequency n^P ∧ |v x-1| ≤ L*inverseFrequency n^P) ∧
--           (∀ a ∈ tests, ∀ y ∈ a.compactSet, ∀ j ≤ N,
--             ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt ThreeModel a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
--             ‖iteratedFDeriv ℝ j ((fun x => z x-1) ∘ (chartAt ThreeModel a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
--             ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt ThreeModel a.center).symm) y‖ ≤ L*inverseFrequency n^P) ∧
--           ENNReal.ofReal (A*(productWaveFrequency n)) < SignTests.signCertificate
--             (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
--             (fun a => ε/((productWaveFrequency n)*ℓ a.val))
--             ((U ∘ threeNormalInv) ∘ normalWaveEquiv)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.normalWaveEquiv` and `OAI.YauCounterexamples.SignTests.signCertificate` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair`, `OAI.YauCounterexamples.inverseFrequency`, `OAI.YauCounterexamples.productFrequency`, `OAI.YauCounterexamples.productWaveFrequency`, `OAI.YauCounterexamples.threeCouplingRadius` and `OAI.YauCounterexamples.weightedLaplacian` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.ThreeCleanBall`, `OAI.YauCounterexamples.threeBackgroundMetric` and `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.intrinsicCorrectionB` and `OAI.YauCounterexamples.intrinsicCorrectionS` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.threeCoupled` and `OAI.YauCounterexamples.threeWaveLift` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.CoordinateTest`, `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsSmoothNeighborhood`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_exact_stage` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean (declaration OAI.YauCounterexamples.exists_three_scalar_producer)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

theorem exists_three_scalar_producer :
    ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric∈N ∧
      ∀ g∈N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∀ F : Set ThreeManifold, IsClosed F → F⊆threeNormalInv '' closedBall 0 a →
      (∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
        g.inner q v w=threeBackgroundMetric.inner q v w) → ∀ A : ℝ,
    ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
    ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
      (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
    ∀ (tests : List (CoordinateTest ThreeModel ThreeManifold)) (N P : ℕ),
      ∃ L > 0, ∀ᶠ n : ℕ in atTop,
      ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
        tsupport u ⊆ ball 0 ((b+R/2)/2) ∧
      let U := threeCoupled threeCouplingRadius n+threeWaveLift u
      let b := intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) U
      let z := intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) U
      (∀ x, U x=0 → 0 < coordinateGradientPair g U U x) ∧
      ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ b ∧
      ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ z ∧
      (∀ x, 0 < b x ∧ 0 < z x) ∧
      (∀ x, weightedLaplacian g b U x+productFrequency n*z x*U x=0) ∧
      tsupport (fun x => b x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+productFrequency n*U x) ∧
      tsupport (fun x => z x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+productFrequency n*U x) ∧
      ∃ v : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
        (∀ x, weightedLaplacian g b v x = productFrequency n*b x^3*v x^5-productFrequency n*z x*v x) ∧
        (∀ x, |b x-1| ≤ L*inverseFrequency n^P ∧
          |z x-1| ≤ L*inverseFrequency n^P ∧ |v x-1| ≤ L*inverseFrequency n^P) ∧
        (∀ a ∈ tests, ∀ y ∈ a.compactSet, ∀ j ≤ N,
          ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt ThreeModel a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => z x-1) ∘ (chartAt ThreeModel a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt ThreeModel a.center).symm) y‖ ≤ L*inverseFrequency n^P) ∧
        ENNReal.ofReal (A*(productWaveFrequency n)) < SignTests.signCertificate
          (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
          (fun a => ε/((productWaveFrequency n)*ℓ a.val))
          ((U ∘ threeNormalInv) ∘ normalWaveEquiv) := by
  sorry

end YauCounterexamples
end

end OAI
end
