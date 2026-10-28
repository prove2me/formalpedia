-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_spherical_wave_background_chart_bounds
-- name    : OAI.YauCounterexamples.spherical_wave_background_chart_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:49:09.937607+00:00
-- url     : https://prove2.me/theorems/892caaf7-b753-4e1f-a46e-1d45e258d98c
-- title:
--   OAI.YauCounterexamples.spherical_wave_background_chart_bounds: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.spherical_wave_background_chart_bounds` of [lean/OAI/Geometry/SmoothYau/Smoothness/ThreeCoupledCleanChartJets.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ThreeCoupledCleanChartJets.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   theorem spherical_wave_background_chart_bounds
--       (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       {F : Set (Sphere 3)} (hF : IsClosed F)
--       (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
--         g.inner q v w=g₀.inner q v w)
--       {φ : Sphere 3 → ℝ} (hφ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ)
--       (hgap : ∀ q ∈ F, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
--         Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q)
--       (p : Sphere 3) {K : Set (Euclidean 3)} (hK : IsCompact K)
--       {r : ℝ} (hr : r < 1) (m D : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
--       ∃ C > 0, ∀ᶠ n : ℕ in atTop,
--       ∀ (u : Euclidean 3 → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
--         tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
--           ((chartAt (Euclidean 3) sourcePole).symm y) < r} →
--         (∀ y : Euclidean 3, ∀ j ≤ m,
--           ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(n:ℝ)^(j+4)*
--             Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm y)) ∧
--           ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (sphereChartMetric g sourcePole) u y+
--             sphereFrequency n*u y) y‖ ≤ C₀*((n:ℝ)^(D+1))⁻¹*
--             Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm y))) →
--         ∀ y ∈ K, ∀ j ≤ m,
--           ‖iteratedFDeriv ℝ j ((roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) ∘
--             (chartAt (Euclidean 3) p).symm) y‖ ≤
--             C*(n:ℝ)^(j+4)*sphericalWeight φ n ((chartAt (Euclidean 3) p).symm y) ∧
--           ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
--             (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
--             sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ∘
--             (chartAt (Euclidean 3) p).symm) y‖ ≤
--             C*(n:ℝ)^4/(n:ℝ)^D*sphericalWeight φ n ((chartAt (Euclidean 3) p).symm y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.sourceAxisOne`, `OAI.YauCounterexamples.sourceAxisTwo`, `OAI.YauCounterexamples.sourcePole` and `OAI.YauCounterexamples.sphericalRadius` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.sphereFrequency` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.sphereChartMetric` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.roundPower` and `OAI.YauCounterexamples.sphericalWaveLift` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.sphericalWeight` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_global_quasimodes` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ThreeCoupledCleanChartJets.lean (declaration OAI.YauCounterexamples.spherical_wave_background_chart_bounds)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007
import Definitions.Def_OAIQ070A008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold
open scoped Topology ContDiff InnerProductSpace

theorem spherical_wave_background_chart_bounds
    (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    {φ : Sphere 3 → ℝ} (hφ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ)
    (hgap : ∀ q ∈ F, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
      Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q)
    (p : Sphere 3) {K : Set (Euclidean 3)} (hK : IsCompact K)
    {r : ℝ} (hr : r < 1) (m D : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
    ∀ (u : Euclidean 3 → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) < r} →
      (∀ y : Euclidean 3, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j u y‖ ≤ C₀*(n:ℝ)^(j+4)*
          Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm y)) ∧
        ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (sphereChartMetric g sourcePole) u y+
          sphereFrequency n*u y) y‖ ≤ C₀*((n:ℝ)^(D+1))⁻¹*
          Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm y))) →
      ∀ y ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j ((roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) ∘
          (chartAt (Euclidean 3) p).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*sphericalWeight φ n ((chartAt (Euclidean 3) p).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
          (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
          sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ∘
          (chartAt (Euclidean 3) p).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*sphericalWeight φ n ((chartAt (Euclidean 3) p).symm y) := by
  sorry

end

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end
