-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_three_global_quasimodes
-- name    : OAI.YauCounterexamples.exists_three_global_quasimodes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:07:14.577398+00:00
-- url     : https://prove2.me/theorems/ff0ae184-cf83-4fcb-88dc-b9f72bd5e9be
-- title:
--   OAI.YauCounterexamples.exists_three_global_quasimodes: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_three_global_quasimodes` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric MeasureTheory BoxIntegral`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   theorem exists_three_global_quasimodes :
--       ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
--         IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
--         ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
--         ∀ F : Set ThreeManifold, IsClosed F → F⊆threeNormalInv '' closedBall 0 a →
--         (∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
--           g.inner q v w=threeBackgroundMetric.inner q v w) → ∀ A : ℝ,
--         ∃ Φ : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ Φ ∧
--           ContDiff ℝ ∞ (Φ ∘ threeNormalInv) ∧ ∃ δ>0,
--           (∀ y∈closedBall 0 a, threeGlobalLog (threeNormalInv y)+δ<Φ (threeNormalInv y)) ∧
--           (∀ p ∉ threeNormalInv '' closedBall 0 b, Φ p ≤ threeGlobalLog p-2*δ) ∧
--           ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
--           ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
--             (∀ J∈partition, 0<ℓ J) ∧ ∃ ε>0,
--           ∀ (ι : Type) [Fintype ι] (p : ι → ThreeManifold) (K : ι → Set ThreeModel),
--             (∀ i, IsCompact (K i)) → ∀ m D : ℕ, ∃ C>0, ∀ᶠ k : ℕ in atTop,
--             ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
--               tsupport u ⊆ ball 0 ((b+R/2)/2) ∧
--               (∀ q : ThreeManifold, threeWeight Φ k q/productWaveFrequency k^111  ≤
--                 |(threeCoupled threeCouplingRadius k+threeWaveLift u) q|+
--                   Real.sqrt (coordinateGradientPair g
--                     (threeCoupled threeCouplingRadius k+threeWaveLift u)
--                     (threeCoupled threeCouplingRadius k+threeWaveLift u) q)/productWaveFrequency k) ∧
--               (∀ i, ∀ y∈K i, ∀ j  ≤  m,
--                 ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius k+threeWaveLift u) ∘
--                   (chartAt ThreeModel (p i)).symm) y‖  ≤
--                   C*productWaveFrequency k^(j+4)*threeWeight Φ k ((chartAt ThreeModel (p i)).symm y) ∧
--                 ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
--                   (threeCoupled threeCouplingRadius k+threeWaveLift u) q+
--                     productFrequency k*(threeCoupled threeCouplingRadius k+threeWaveLift u) q) ∘
--                   (chartAt ThreeModel (p i)).symm) y‖  ≤
--                   C*productWaveFrequency k^4/productWaveFrequency k^D*
--                     threeWeight Φ k ((chartAt ThreeModel (p i)).symm y)) ∧
--               ENNReal.ofReal (A*productWaveFrequency k) < SignTests.signCertificate
--                 (fun z : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo z.val)
--                 (fun z => ε/(productWaveFrequency k*ℓ z.val))
--                 (((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) ∘ normalWaveEquiv) ∧
--               ENNReal.ofReal (A*productWaveFrequency k) < 36*Measure.hausdorffMeasure 2
--                 ((⋃ z : {J : Box (Fin 3) // J∈partition.boxes}, Box.Ioo z.val) ∩
--                   {x | ((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) (normalWaveEquiv x)=0})
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.normalWaveEquiv` and `OAI.YauCounterexamples.SignTests.signCertificate` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair`, `OAI.YauCounterexamples.productFrequency`, `OAI.YauCounterexamples.productWaveFrequency` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.ThreeCleanBall`, `OAI.YauCounterexamples.threeBackgroundMetric` and `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeCoupled`, `OAI.YauCounterexamples.threeGlobalLog`, `OAI.YauCounterexamples.threeWaveLift` and `OAI.YauCounterexamples.threeWeight` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsSmoothNeighborhood`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_scalar_producer` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ExistsThreeScalarProducer.lean (declaration OAI.YauCounterexamples.exists_three_global_quasimodes)

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

section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal
theorem exists_three_global_quasimodes :
    ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
      ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∀ F : Set ThreeManifold, IsClosed F → F⊆threeNormalInv '' closedBall 0 a →
      (∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
        g.inner q v w=threeBackgroundMetric.inner q v w) → ∀ A : ℝ,
      ∃ Φ : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ Φ ∧
        ContDiff ℝ ∞ (Φ ∘ threeNormalInv) ∧ ∃ δ>0,
        (∀ y∈closedBall 0 a, threeGlobalLog (threeNormalInv y)+δ<Φ (threeNormalInv y)) ∧
        (∀ p ∉ threeNormalInv '' closedBall 0 b, Φ p ≤ threeGlobalLog p-2*δ) ∧
        ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
        ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
          (∀ J∈partition, 0<ℓ J) ∧ ∃ ε>0,
        ∀ (ι : Type) [Fintype ι] (p : ι → ThreeManifold) (K : ι → Set ThreeModel),
          (∀ i, IsCompact (K i)) → ∀ m D : ℕ, ∃ C>0, ∀ᶠ k : ℕ in atTop,
          ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
            tsupport u ⊆ ball 0 ((b+R/2)/2) ∧
            (∀ q : ThreeManifold, threeWeight Φ k q/productWaveFrequency k^111  ≤
              |(threeCoupled threeCouplingRadius k+threeWaveLift u) q|+
                Real.sqrt (coordinateGradientPair g
                  (threeCoupled threeCouplingRadius k+threeWaveLift u)
                  (threeCoupled threeCouplingRadius k+threeWaveLift u) q)/productWaveFrequency k) ∧
            (∀ i, ∀ y∈K i, ∀ j  ≤  m,
              ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius k+threeWaveLift u) ∘
                (chartAt ThreeModel (p i)).symm) y‖  ≤
                C*productWaveFrequency k^(j+4)*threeWeight Φ k ((chartAt ThreeModel (p i)).symm y) ∧
              ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
                (threeCoupled threeCouplingRadius k+threeWaveLift u) q+
                  productFrequency k*(threeCoupled threeCouplingRadius k+threeWaveLift u) q) ∘
                (chartAt ThreeModel (p i)).symm) y‖  ≤
                C*productWaveFrequency k^4/productWaveFrequency k^D*
                  threeWeight Φ k ((chartAt ThreeModel (p i)).symm y)) ∧
            ENNReal.ofReal (A*productWaveFrequency k) < SignTests.signCertificate
              (fun z : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo z.val)
              (fun z => ε/(productWaveFrequency k*ℓ z.val))
              (((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) ∘ normalWaveEquiv) ∧
            ENNReal.ofReal (A*productWaveFrequency k) < 36*Measure.hausdorffMeasure 2
              ((⋃ z : {J : Box (Fin 3) // J∈partition.boxes}, Box.Ioo z.val) ∩
                {x | ((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) (normalWaveEquiv x)=0}) := by
  sorry
end

open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

end YauCounterexamples
end

end OAI
end
