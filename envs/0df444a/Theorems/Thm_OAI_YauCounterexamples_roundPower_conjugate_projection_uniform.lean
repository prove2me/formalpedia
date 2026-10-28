-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_roundPower_conjugate_projection_uniform
-- name    : OAI.YauCounterexamples.roundPower_conjugate_projection_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:47:55.232306+00:00
-- url     : https://prove2.me/theorems/e6658ac8-0469-4150-b877-2f563e40b352
-- title:
--   OAI.YauCounterexamples.roundPower_conjugate_projection_uniform: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.roundPower_conjugate_projection_uniform` of [lean/OAI/Geometry/SmoothYau/Estimates/RoundPowerConjugateProjectionUniform.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/RoundPowerConjugateProjectionUniform.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold`, `open scoped Topology ContDiff InnerProductSpace Matrix`):
--
--   ```lean
--   theorem roundPower_conjugate_projection_uniform
--       (g : SmoothMetric (Euclidean d) (Sphere d)) (a b : Euclidean (d+1)) (p : Sphere d)
--       (ha : inner ℝ a a=1) (hb : inner ℝ b b=1) (hab : inner ℝ a b=0)
--       {K : Set (Euclidean d)} (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean d) p).target)
--       (hg : ∀ y ∈ K, ∀ v z : TangentSpace 𝓘(ℝ,Euclidean d) ((chartAt (Euclidean d) p).symm y),
--         g.inner _ v z = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
--           (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
--             (fun q : Sphere d => (q : Euclidean (d+1))) _ v)
--           (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
--             (fun q : Sphere d => (q : Euclidean (d+1))) _ z))
--       (h : ℕ) {r t D : ℝ} (hr : 0 < r) (ht : t < 1) (hD : 0 ≤ D)
--       (hKr : ∀ y ∈ K, r ≤ ‖roundPlanarChart a b p y‖)
--       (hKt : ∀ y ∈ K, Complex.normSq (roundPlanarChart a b p y) ≤ t)
--       : ∃ C : ℝ, 0 < C ∧ ∀ (w : Sphere d → ℝ),
--         ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ w →
--         (∀ x, w x ≠ 0) →
--         (∀ y ∈ K, 1/2 ≤ w ((chartAt (Euclidean d) p).symm y)) →
--         (∀ y ∈ K, w ((chartAt (Euclidean d) p).symm y) ≤ 2) →
--         (∀ j : ℕ, 1 ≤ j → j ≤ h+1 → ∀ y ∈ K,
--           ‖iteratedFDeriv ℝ j (w ∘ (chartAt (Euclidean d) p).symm) y‖ ≤ D) →
--         (∀ y ∈ K, coordinateGradientPair g w w ((chartAt (Euclidean d) p).symm y) ≤ (1-t)/16) →
--       ∀ n : ℕ, 1 ≤ n → ∀ y ∈ K, ∀ i j : CoordIndex (Euclidean d),
--         ‖iteratedFDeriv ℝ h (chartGradientProjection g
--           (fun x => roundPower a b n x/w x) p i j) y‖ ≤ C*(n:ℝ)^h
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.coordinateGradientPair` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.chartGradientProjection`, `OAI.YauCounterexamples.roundPlanarChart` and `OAI.YauCounterexamples.roundPower` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.CoordIndex`, `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.spherical_annular_projection_uniform` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/RoundPowerConjugateProjectionUniform.lean (declaration OAI.YauCounterexamples.roundPower_conjugate_projection_uniform)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
variable {d : ℕ}
theorem roundPower_conjugate_projection_uniform
    (g : SmoothMetric (Euclidean d) (Sphere d)) (a b : Euclidean (d+1)) (p : Sphere d)
    (ha : inner ℝ a a=1) (hb : inner ℝ b b=1) (hab : inner ℝ a b=0)
    {K : Set (Euclidean d)} (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean d) p).target)
    (hg : ∀ y ∈ K, ∀ v z : TangentSpace 𝓘(ℝ,Euclidean d) ((chartAt (Euclidean d) p).symm y),
      g.inner _ v z = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
          (fun q : Sphere d => (q : Euclidean (d+1))) _ v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
          (fun q : Sphere d => (q : Euclidean (d+1))) _ z))
    (h : ℕ) {r t D : ℝ} (hr : 0 < r) (ht : t < 1) (hD : 0 ≤ D)
    (hKr : ∀ y ∈ K, r ≤ ‖roundPlanarChart a b p y‖)
    (hKt : ∀ y ∈ K, Complex.normSq (roundPlanarChart a b p y) ≤ t)
    : ∃ C : ℝ, 0 < C ∧ ∀ (w : Sphere d → ℝ),
      ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ w →
      (∀ x, w x ≠ 0) →
      (∀ y ∈ K, 1/2 ≤ w ((chartAt (Euclidean d) p).symm y)) →
      (∀ y ∈ K, w ((chartAt (Euclidean d) p).symm y) ≤ 2) →
      (∀ j : ℕ, 1 ≤ j → j ≤ h+1 → ∀ y ∈ K,
        ‖iteratedFDeriv ℝ j (w ∘ (chartAt (Euclidean d) p).symm) y‖ ≤ D) →
      (∀ y ∈ K, coordinateGradientPair g w w ((chartAt (Euclidean d) p).symm y) ≤ (1-t)/16) →
    ∀ n : ℕ, 1 ≤ n → ∀ y ∈ K, ∀ i j : CoordIndex (Euclidean d),
      ‖iteratedFDeriv ℝ h (chartGradientProjection g
        (fun x => roundPower a b n x/w x) p i j) y‖ ≤ C*(n:ℝ)^h := by
  sorry
end YauCounterexamples
end

end OAI
end
