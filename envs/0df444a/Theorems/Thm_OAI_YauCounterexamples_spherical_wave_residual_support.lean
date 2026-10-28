-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_spherical_wave_residual_support
-- name    : OAI.YauCounterexamples.spherical_wave_residual_support
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:48:52.667231+00:00
-- url     : https://prove2.me/theorems/aadb9304-df17-4b93-871d-e6d11b2bbf21
-- title:
--   OAI.YauCounterexamples.spherical_wave_residual_support: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.spherical_wave_residual_support` of [lean/OAI/Geometry/SmoothYau/Smoothness/ExistsSphericalRadialCutoff.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ExistsSphericalRadialCutoff.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   theorem spherical_wave_residual_support
--       (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       {F : Set (Sphere 3)} (hF : IsClosed F) {r : ℝ}
--       (hFr : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r)
--       (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
--         g.inner q v w=g₀.inner q v w)
--       {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
--       (hs : tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
--         ((chartAt (Euclidean 3) sourcePole).symm y) < r})
--       {n : ℕ} (hn : 2 ≤ n) :
--       tsupport (fun q => laplaceBeltrami g
--         (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
--         sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ⊆
--         {q | sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r}
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.sourceAxisOne`, `OAI.YauCounterexamples.sourceAxisTwo`, `OAI.YauCounterexamples.sourcePole` and `OAI.YauCounterexamples.sphericalRadius` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.sphereFrequency` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.roundPower` and `OAI.YauCounterexamples.sphericalWaveLift` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_exact_stage` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ExistsSphericalRadialCutoff.lean (declaration OAI.YauCounterexamples.spherical_wave_residual_support)

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

theorem spherical_wave_residual_support
    (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {F : Set (Sphere 3)} (hF : IsClosed F) {r : ℝ}
    (hFr : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < r})
    {n : ℕ} (hn : 2 ≤ n) :
    tsupport (fun q => laplaceBeltrami g
      (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
      sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ⊆
      {q | sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r} := by
  sorry

end YauCounterexamples
end

end OAI
end
