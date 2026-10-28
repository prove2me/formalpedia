-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_spherical_annular_projection_uniform
-- name    : OAI.YauCounterexamples.spherical_annular_projection_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:47:28.288258+00:00
-- url     : https://prove2.me/theorems/432176c1-d9fc-4be5-91b0-ac8d24b9d2dc
-- title:
--   OAI.YauCounterexamples.spherical_annular_projection_uniform: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.spherical_annular_projection_uniform` of [lean/OAI/Geometry/SmoothYau/Geometry/ChartGradientProjectionCongrNhds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ChartGradientProjectionCongrNhds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   theorem spherical_annular_projection_uniform
--       (g₀ g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       {F : Set (Sphere 3)} {r a b : ℝ} (hr : 0 < r) (hra : r < a) (hab : a ≤ b) (hb : b < 1)
--       (hFr : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r)
--       (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
--         g.inner q v w=g₀.inner q v w)
--       (tests : List (CoordinateTest (Euclidean 3) (Sphere 3))) (h : ℕ) {D : ℝ} (hD : 0 ≤ D) :
--       ∃ C > 0, ∀ (w : Sphere 3 → ℝ), ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ w →
--         (∀ q, 1/2 ≤ w q) → (∀ q, w q ≤ 2) →
--         (∀ t ∈ tests, ∀ y ∈ t.compactSet, ∀ j ≤ h+1,
--           ‖iteratedFDeriv ℝ j (w ∘ (chartAt (Euclidean 3) t.center).symm) y‖ ≤ D) →
--         (∀ q, coordinateGradientPair g w w q ≤ (1-b^2)/16) →
--         ∀ {u : Euclidean 3 → ℝ}, HasCompactSupport u →
--         tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
--           ((chartAt (Euclidean 3) sourcePole).symm y) < r} →
--         ∀ n : ℕ, 1 ≤ n → ∀ t ∈ tests, ∀ y ∈ t.compactSet,
--         a ≤ sphericalRadius sourceAxisOne sourceAxisTwo ((chartAt (Euclidean 3) t.center).symm y) →
--         sphericalRadius sourceAxisOne sourceAxisTwo ((chartAt (Euclidean 3) t.center).symm y) ≤ b →
--         ∀ i j : CoordIndex (Euclidean 3), ∀ k ≤ h,
--           ‖iteratedFDeriv ℝ k (chartGradientProjection g
--             (fun q => (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q/w q)
--             t.center i j) y‖ ≤ C*(n:ℝ)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.sourceAxisOne`, `OAI.YauCounterexamples.sourceAxisTwo`, `OAI.YauCounterexamples.sourcePole` and `OAI.YauCounterexamples.sphericalRadius` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.coordinateGradientPair` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.chartGradientProjection`, `OAI.YauCounterexamples.roundPower` and `OAI.YauCounterexamples.sphericalWaveLift` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.CoordIndex`, `OAI.YauCounterexamples.CoordinateTest`, `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_exact_stage` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ChartGradientProjectionCongrNhds.lean (declaration OAI.YauCounterexamples.spherical_annular_projection_uniform)

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
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples

theorem spherical_annular_projection_uniform
    (g₀ g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {F : Set (Sphere 3)} {r a b : ℝ} (hr : 0 < r) (hra : r < a) (hab : a ≤ b) (hb : b < 1)
    (hFr : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (tests : List (CoordinateTest (Euclidean 3) (Sphere 3))) (h : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C > 0, ∀ (w : Sphere 3 → ℝ), ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ w →
      (∀ q, 1/2 ≤ w q) → (∀ q, w q ≤ 2) →
      (∀ t ∈ tests, ∀ y ∈ t.compactSet, ∀ j ≤ h+1,
        ‖iteratedFDeriv ℝ j (w ∘ (chartAt (Euclidean 3) t.center).symm) y‖ ≤ D) →
      (∀ q, coordinateGradientPair g w w q ≤ (1-b^2)/16) →
      ∀ {u : Euclidean 3 → ℝ}, HasCompactSupport u →
      tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) < r} →
      ∀ n : ℕ, 1 ≤ n → ∀ t ∈ tests, ∀ y ∈ t.compactSet,
      a ≤ sphericalRadius sourceAxisOne sourceAxisTwo ((chartAt (Euclidean 3) t.center).symm y) →
      sphericalRadius sourceAxisOne sourceAxisTwo ((chartAt (Euclidean 3) t.center).symm y) ≤ b →
      ∀ i j : CoordIndex (Euclidean 3), ∀ k ≤ h,
        ‖iteratedFDeriv ℝ k (chartGradientProjection g
          (fun q => (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q/w q)
          t.center i j) y‖ ≤ C*(n:ℝ)^k := by
  sorry
end YauCounterexamples
end

end OAI
end
