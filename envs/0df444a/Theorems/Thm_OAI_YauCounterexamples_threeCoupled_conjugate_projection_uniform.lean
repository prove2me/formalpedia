-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_threeCoupled_conjugate_projection_uniform
-- name    : OAI.YauCounterexamples.threeCoupled_conjugate_projection_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:10:49.395696+00:00
-- url     : https://prove2.me/theorems/03e4dbef-689a-4345-864e-f95ab53d4e5c
-- title:
--   OAI.YauCounterexamples.threeCoupled_conjugate_projection_uniform: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.threeCoupled_conjugate_projection_uniform` of [lean/OAI/Geometry/SmoothYau/Smoothness/ThreeCoupledCleanChartJets.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ThreeCoupledCleanChartJets.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold`, `open scoped Topology ContDiff InnerProductSpace Matrix`):
--
--   ```lean
--   theorem threeCoupled_conjugate_projection_uniform
--       (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold)
--       {K : Set ThreeModel} (hK : IsCompact K)
--       (hKO : K ⊆ (chartAt ThreeModel p).target)
--       (hg : ∀ y ∈ K, ∀ v z : TangentSpace 𝓘(ℝ,ThreeModel) ((chartAt ThreeModel p).symm y),
--         g.inner _ v z = threeBackgroundMetric.inner _ v z)
--       (h : ℕ) {D : ℝ} (hD : 0 ≤ D)
--       (hKr : ∀ y ∈ K, 1/2 ≤ ‖productA ((chartAt ThreeModel p).symm y).1‖)
--       (hKt : ∀ y ∈ K, ‖productA ((chartAt ThreeModel p).symm y).1‖ ≤ 3/4)
--       : ∃ C : ℝ, 0 < C ∧ ∀ (w : ThreeManifold → ℝ),
--         ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ w →
--         (∀ x, w x ≠ 0) →
--         (∀ y ∈ K, 1/2 ≤ w ((chartAt ThreeModel p).symm y)) →
--         (∀ y ∈ K, w ((chartAt ThreeModel p).symm y) ≤ 2) →
--         (∀ j : ℕ, 1 ≤ j → j ≤ h+1 → ∀ y ∈ K,
--           ‖iteratedFDeriv ℝ j (w ∘ (chartAt ThreeModel p).symm) y‖ ≤ D) →
--         (∀ y ∈ K, coordinateGradientPair g w w ((chartAt ThreeModel p).symm y) ≤ 1/4096) →
--       ∀ n : ℕ, 1 ≤ n → ∀ y ∈ K, ∀ i j : CoordIndex ThreeModel,
--         ‖iteratedFDeriv ℝ h (chartGradientProjection g
--           (fun x => threeCoupled threeCouplingRadius n x/w x) p i j) y‖ ≤ C*(n:ℝ)^h
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.productA`, `OAI.YauCounterexamples.threeChartedSpace` and `OAI.YauCounterexamples.threeIsManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.threeBackgroundMetric` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.chartGradientProjection` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.threeCoupled` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.CoordIndex`, `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.three_annular_projection_uniform` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ThreeCoupledCleanChartJets.lean (declaration OAI.YauCounterexamples.threeCoupled_conjugate_projection_uniform)

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

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

theorem threeCoupled_conjugate_projection_uniform
    (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold)
    {K : Set ThreeModel} (hK : IsCompact K)
    (hKO : K ⊆ (chartAt ThreeModel p).target)
    (hg : ∀ y ∈ K, ∀ v z : TangentSpace 𝓘(ℝ,ThreeModel) ((chartAt ThreeModel p).symm y),
      g.inner _ v z = threeBackgroundMetric.inner _ v z)
    (h : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hKr : ∀ y ∈ K, 1/2 ≤ ‖productA ((chartAt ThreeModel p).symm y).1‖)
    (hKt : ∀ y ∈ K, ‖productA ((chartAt ThreeModel p).symm y).1‖ ≤ 3/4)
    : ∃ C : ℝ, 0 < C ∧ ∀ (w : ThreeManifold → ℝ),
      ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ w →
      (∀ x, w x ≠ 0) →
      (∀ y ∈ K, 1/2 ≤ w ((chartAt ThreeModel p).symm y)) →
      (∀ y ∈ K, w ((chartAt ThreeModel p).symm y) ≤ 2) →
      (∀ j : ℕ, 1 ≤ j → j ≤ h+1 → ∀ y ∈ K,
        ‖iteratedFDeriv ℝ j (w ∘ (chartAt ThreeModel p).symm) y‖ ≤ D) →
      (∀ y ∈ K, coordinateGradientPair g w w ((chartAt ThreeModel p).symm y) ≤ 1/4096) →
    ∀ n : ℕ, 1 ≤ n → ∀ y ∈ K, ∀ i j : CoordIndex ThreeModel,
      ‖iteratedFDeriv ℝ h (chartGradientProjection g
        (fun x => threeCoupled threeCouplingRadius n x/w x) p i j) y‖ ≤ C*(n:ℝ)^h := by
  sorry

end YauCounterexamples
end

end OAI
end
