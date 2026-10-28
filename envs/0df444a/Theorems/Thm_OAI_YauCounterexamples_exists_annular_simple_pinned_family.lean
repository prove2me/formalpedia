-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_annular_simple_pinned_family
-- name    : OAI.YauCounterexamples.exists_annular_simple_pinned_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:37:45.155257+00:00
-- url     : https://prove2.me/theorems/fd5bdbb3-ce94-41c0-887a-46358680e042
-- title:
--   OAI.YauCounterexamples.exists_annular_simple_pinned_family: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_annular_simple_pinned_family` of [lean/OAI/Geometry/SmoothYau/Estimates/ExistsAnnularSimplePinnedFamily.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/ExistsAnnularSimplePinnedFamily.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   theorem exists_annular_simple_pinned_family
--       (I : MetricIntegralAtlas (E := Euclidean 3) (M := Sphere 3))
--       (g : SmoothMetric (Euclidean 3) (Sphere 3))
--       (a b c : Euclidean 4)
--       (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
--       (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
--       (n : ℕ) (hn : 2 ≤ n) {l h : ℝ} (hl : 0 < l) (hlh : l < h) (hh : h < 1)
--       (u : RealSmoothFunctions (Euclidean 3) (Sphere 3))
--       (hu0 : (u : Sphere 3 → ℝ) ≠ 0)
--       (hue : ∀ p, -laplaceBeltrami g u p = ((n:ℝ)*((n:ℝ)+2))*u p)
--       (hup : ∀ p : Sphere 3, l < Complex.normSq (planarLinear a b p) →
--         Complex.normSq (planarLinear a b p) < h → u p = roundPower a b n p)
--       (hgp : ∀ p : Sphere 3, l < Complex.normSq (planarLinear a b p) →
--         Complex.normSq (planarLinear a b p) < h →
--         ∀ (X Y : TangentSpace 𝓘(ℝ,Euclidean 3) p),
--           g.inner p X Y = (inner ℝ : Euclidean 4 → Euclidean 4 → ℝ)
--             (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4)
--               (fun q : Sphere 3 => (q : Euclidean 4)) p X)
--             (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4)
--               (fun q : Sphere 3 => (q : Euclidean 4)) p Y))
--       : ∃ K : pinningTensorSpace g (u : Sphere 3 → ℝ)
--         {p | l < Complex.normSq (planarLinear a b p) ∧ Complex.normSq (planarLinear a b p) < h},
--         ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ v : Sphere 3 → ℝ,
--           ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v →
--           (∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) v x =
--             ((n:ℝ)*((n:ℝ)+2))*v x) → ∃ c : ℝ, v = fun x => c*u x
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.MetricIntegralAtlas` (definitions bundle `OAIQ070A001` of this split); `OAI.YauCounterexamples.RealSmoothFunctions` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.metricGradient` and `OAI.YauCounterexamples.planarLinear` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.pinnedMetric`, `OAI.YauCounterexamples.pinningTensorSpace` and `OAI.YauCounterexamples.roundPower` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.spherical_pin_near` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/ExistsAnnularSimplePinnedFamily.lean (declaration OAI.YauCounterexamples.exists_annular_simple_pinned_family)

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
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
namespace YauCounterexamples

theorem exists_annular_simple_pinned_family
    (I : MetricIntegralAtlas (E := Euclidean 3) (M := Sphere 3))
    (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (a b c : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (n : ℕ) (hn : 2 ≤ n) {l h : ℝ} (hl : 0 < l) (hlh : l < h) (hh : h < 1)
    (u : RealSmoothFunctions (Euclidean 3) (Sphere 3))
    (hu0 : (u : Sphere 3 → ℝ) ≠ 0)
    (hue : ∀ p, -laplaceBeltrami g u p = ((n:ℝ)*((n:ℝ)+2))*u p)
    (hup : ∀ p : Sphere 3, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h → u p = roundPower a b n p)
    (hgp : ∀ p : Sphere 3, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h →
      ∀ (X Y : TangentSpace 𝓘(ℝ,Euclidean 3) p),
        g.inner p X Y = (inner ℝ : Euclidean 4 → Euclidean 4 → ℝ)
          (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4)
            (fun q : Sphere 3 => (q : Euclidean 4)) p X)
          (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4)
            (fun q : Sphere 3 => (q : Euclidean 4)) p Y))
    : ∃ K : pinningTensorSpace g (u : Sphere 3 → ℝ)
      {p | l < Complex.normSq (planarLinear a b p) ∧ Complex.normSq (planarLinear a b p) < h},
      ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ v : Sphere 3 → ℝ,
        ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v →
        (∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) v x =
          ((n:ℝ)*((n:ℝ)+2))*v x) → ∃ c : ℝ, v = fun x => c*u x := by
  sorry
end YauCounterexamples
end

end OAI
end
