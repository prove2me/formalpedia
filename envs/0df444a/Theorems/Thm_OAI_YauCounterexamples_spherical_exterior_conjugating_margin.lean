-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_spherical_exterior_conjugating_margin
-- name    : OAI.YauCounterexamples.spherical_exterior_conjugating_margin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:50:56.428012+00:00
-- url     : https://prove2.me/theorems/f480186e-ce1e-4de4-880d-281e6cae0151
-- title:
--   OAI.YauCounterexamples.spherical_exterior_conjugating_margin: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.spherical_exterior_conjugating_margin` of [lean/OAI/Geometry/SmoothYau/Spectrum/InverseFrequencyWeightedZero.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/InverseFrequencyWeightedZero.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold BoxIntegral`, `open scoped Topology ContDiff ENNReal InnerProductSpace`):
--
--   ```lean
--   lemma spherical_exterior_conjugating_margin
--       (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       (g : SmoothMetric (Euclidean 3) (Sphere 3))
--       {r a b : ℝ} (hr0 : 0 < r) (hra : r < a) (hb0 : 0 ≤ b) (hb2 : b^2 < 1)
--       {F : Set (Sphere 3)} (hFr : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r)
--       (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
--         g.inner q v w=g₀.inner q v w)
--       {u : Euclidean 3 → ℝ} (huc : HasCompactSupport u)
--       (hus : tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
--         ((chartAt (Euclidean 3) sourcePole).symm y) < r})
--       (n : ℕ) (hn : 1 ≤ n) (w : Sphere 3 → ℝ)
--       (hwl : ∀ q, 1/2 ≤ w q) (hwG : ∀ q, coordinateGradientPair g w w q ≤ (1-b^2)/16)
--       (q : Sphere 3) (hqa : a ≤ sphericalRadius sourceAxisOne sourceAxisTwo q)
--       (hqb : sphericalRadius sourceAxisOne sourceAxisTwo q ≤ b) :
--       let U := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u
--       U q^2*coordinateGradientPair g w w q < w q^2*coordinateGradientPair g U U q
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.sourceAxisOne`, `OAI.YauCounterexamples.sourceAxisTwo`, `OAI.YauCounterexamples.sourcePole` and `OAI.YauCounterexamples.sphericalRadius` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.coordinateGradientPair` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.roundPower` and `OAI.YauCounterexamples.sphericalWaveLift` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_exact_stage` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Spectrum/InverseFrequencyWeightedZero.lean (declaration OAI.YauCounterexamples.spherical_exterior_conjugating_margin)

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
open Set Filter Function Manifold BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace
namespace YauCounterexamples

lemma spherical_exterior_conjugating_margin
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3))
    {r a b : ℝ} (hr0 : 0 < r) (hra : r < a) (hb0 : 0 ≤ b) (hb2 : b^2 < 1)
    {F : Set (Sphere 3)} (hFr : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    {u : Euclidean 3 → ℝ} (huc : HasCompactSupport u)
    (hus : tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < r})
    (n : ℕ) (hn : 1 ≤ n) (w : Sphere 3 → ℝ)
    (hwl : ∀ q, 1/2 ≤ w q) (hwG : ∀ q, coordinateGradientPair g w w q ≤ (1-b^2)/16)
    (q : Sphere 3) (hqa : a ≤ sphericalRadius sourceAxisOne sourceAxisTwo q)
    (hqb : sphericalRadius sourceAxisOne sourceAxisTwo q ≤ b) :
    let U := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u
    U q^2*coordinateGradientPair g w w q < w q^2*coordinateGradientPair g U U q := by
  sorry

end YauCounterexamples
end

end OAI
end
