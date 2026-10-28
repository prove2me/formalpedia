-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_three_annular_projection_uniform
-- name    : OAI.YauCounterexamples.three_annular_projection_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:12:57.938106+00:00
-- url     : https://prove2.me/theorems/6ef7c2ee-a485-4819-94d7-87fb468512c3
-- title:
--   OAI.YauCounterexamples.three_annular_projection_uniform: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.three_annular_projection_uniform` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   theorem three_annular_projection_uniform
--       (g : SmoothMetric ThreeModel ThreeManifold)
--       {F : Set ThreeManifold} {c d e R : ℝ} (hcd : c<d) (heR : e≤R)
--       (hclean : ThreeCleanBall R) (hFc : F⊆threeNormalInv '' closedBall 0 c)
--       (hext : ∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
--         g.inner q v w=threeBackgroundMetric.inner q v w)
--       (tests : List (CoordinateTest ThreeModel ThreeManifold)) (h : ℕ) {D : ℝ} (hD : 0≤D) :
--       ∃ C>0, ∀ w : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ w →
--         (∀ q, 1/2≤w q) → (∀ q, w q≤2) →
--         (∀ t∈tests, ∀ y∈t.compactSet, ∀ j≤h+1,
--           ‖iteratedFDeriv ℝ j (w ∘ (chartAt ThreeModel t.center).symm) y‖≤D) →
--         (∀ q, coordinateGradientPair g w w q≤1/4096) →
--         ∀ {u : NormalWaveSpace → ℝ}, HasCompactSupport u → tsupport u⊆closedBall 0 c →
--         ∀ n : ℕ, 1≤n → ∀ t∈tests, ∀ y∈t.compactSet,
--         (chartAt ThreeModel t.center).symm y∈ThreeAnnulus d e →
--         ∀ i j : CoordIndex ThreeModel, ∀ k≤h,
--           ‖iteratedFDeriv ℝ k (chartGradientProjection g
--             (fun q => (threeCoupled threeCouplingRadius n+threeWaveLift u) q/w q)
--             t.center i j) y‖≤C*(n:ℝ)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.ThreeAnnulus`, `OAI.YauCounterexamples.ThreeCleanBall`, `OAI.YauCounterexamples.threeBackgroundMetric` and `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.chartGradientProjection` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.threeCoupled` and `OAI.YauCounterexamples.threeWaveLift` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.CoordIndex`, `OAI.YauCounterexamples.CoordinateTest`, `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_exact_stage` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeCutoffControlBounds.lean (declaration OAI.YauCounterexamples.three_annular_projection_uniform)

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
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
theorem three_annular_projection_uniform
    (g : SmoothMetric ThreeModel ThreeManifold)
    {F : Set ThreeManifold} {c d e R : ℝ} (hcd : c<d) (heR : e≤R)
    (hclean : ThreeCleanBall R) (hFc : F⊆threeNormalInv '' closedBall 0 c)
    (hext : ∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
      g.inner q v w=threeBackgroundMetric.inner q v w)
    (tests : List (CoordinateTest ThreeModel ThreeManifold)) (h : ℕ) {D : ℝ} (hD : 0≤D) :
    ∃ C>0, ∀ w : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ w →
      (∀ q, 1/2≤w q) → (∀ q, w q≤2) →
      (∀ t∈tests, ∀ y∈t.compactSet, ∀ j≤h+1,
        ‖iteratedFDeriv ℝ j (w ∘ (chartAt ThreeModel t.center).symm) y‖≤D) →
      (∀ q, coordinateGradientPair g w w q≤1/4096) →
      ∀ {u : NormalWaveSpace → ℝ}, HasCompactSupport u → tsupport u⊆closedBall 0 c →
      ∀ n : ℕ, 1≤n → ∀ t∈tests, ∀ y∈t.compactSet,
      (chartAt ThreeModel t.center).symm y∈ThreeAnnulus d e →
      ∀ i j : CoordIndex ThreeModel, ∀ k≤h,
        ‖iteratedFDeriv ℝ k (chartGradientProjection g
          (fun q => (threeCoupled threeCouplingRadius n+threeWaveLift u) q/w q)
          t.center i j) y‖≤C*(n:ℝ)^k := by
  sorry
end

open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

end YauCounterexamples
end

end OAI
end
