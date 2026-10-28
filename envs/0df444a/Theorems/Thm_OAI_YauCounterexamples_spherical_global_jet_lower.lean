-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_spherical_global_jet_lower
-- name    : OAI.YauCounterexamples.spherical_global_jet_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:48:16.955288+00:00
-- url     : https://prove2.me/theorems/5aa9c729-563e-4c16-afcb-73cb4203df8e
-- title:
--   OAI.YauCounterexamples.spherical_global_jet_lower: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.spherical_global_jet_lower` of [lean/OAI/Geometry/SmoothYau/Smoothness/ThreeCoupledCleanChartJets.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ThreeCoupledCleanChartJets.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem spherical_global_jet_lower
--       (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       {φ : Sphere 3 → ℝ} {t : ℝ}
--       (hin : ∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
--         sphericalRadius sourceAxisOne sourceAxisTwo q < t →
--         Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q)
--       {F : Set (Sphere 3)} (hF : F ⊆ {q | sphericalRadius sourceAxisOne sourceAxisTwo q < t})
--       (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
--         g.inner q v w=g₀.inner q v w)
--       (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
--         ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
--       {n : ℕ} (hn : 2 ≤ n) (C : ℝ) (hnC : 2*C ≤ (n:ℝ)^2)
--       (hcover : ∀ q : Sphere 3, ‖planarLinear sourceAxisOne sourceAxisTwo q‖^n ≤
--         (n:ℝ)^6*Real.exp ((n:ℝ)*φ q) → sphericalRadius sourceAxisOne sourceAxisTwo q ≤ 3/10)
--       {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
--       (hsmall : ∀ q : Sphere 3, |sphericalWaveLift u q|+
--         ‖fderiv ℝ (sphericalWaveLift u ∘ (chartAt (Euclidean 3) q).symm) 0‖/(n:ℝ) ≤
--           C*(n:ℝ)^4*Real.exp ((n:ℝ)*φ q))
--       (hjet : ∀ y ∈ sphericalExceptionalInChart φ n,
--         1/(n:ℝ)^110 ≤ ‖realWaveJet n (sphericalChartWeight φ n y)
--           (((roundPower sourceAxisOne sourceAxisTwo n ∘
--             (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) y‖) :
--       ∀ q : Sphere 3, sphericalWeight φ n q/(n:ℝ)^110 ≤
--         |(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q|+
--         Real.sqrt (coordinateGradientPair g
--           (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u)
--           (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q)/(n:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.normalWaveEquiv`, `OAI.YauCounterexamples.selfMetricFlat`, `OAI.YauCounterexamples.sourceAxisOne`, `OAI.YauCounterexamples.sourceAxisTwo`, `OAI.YauCounterexamples.sourcePole`, `OAI.YauCounterexamples.sphericalCoverage` and `OAI.YauCounterexamples.sphericalRadius` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.planarLinear` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.coordinateGradientPair` and `OAI.YauCounterexamples.realWaveJet` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.sphereChartMetric` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.roundPower`, `OAI.YauCounterexamples.sphericalChartWeight`, `OAI.YauCounterexamples.sphericalExceptionalInChart` and `OAI.YauCounterexamples.sphericalWaveLift` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.sphericalWeight` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.SmoothMetric` and `OAI.YauCounterexamples.Sphere` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_global_quasimodes` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ThreeCoupledCleanChartJets.lean (declaration OAI.YauCounterexamples.spherical_global_jet_lower)

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
open scoped Topology ContDiff

theorem spherical_global_jet_lower
    (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {φ : Sphere 3 → ℝ} {t : ℝ}
    (hin : ∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
      sphericalRadius sourceAxisOne sourceAxisTwo q < t →
      Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q)
    {F : Set (Sphere 3)} (hF : F ⊆ {q | sphericalRadius sourceAxisOne sourceAxisTwo q < t})
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    {n : ℕ} (hn : 2 ≤ n) (C : ℝ) (hnC : 2*C ≤ (n:ℝ)^2)
    (hcover : ∀ q : Sphere 3, ‖planarLinear sourceAxisOne sourceAxisTwo q‖^n ≤
      (n:ℝ)^6*Real.exp ((n:ℝ)*φ q) → sphericalRadius sourceAxisOne sourceAxisTwo q ≤ 3/10)
    {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hsmall : ∀ q : Sphere 3, |sphericalWaveLift u q|+
      ‖fderiv ℝ (sphericalWaveLift u ∘ (chartAt (Euclidean 3) q).symm) 0‖/(n:ℝ) ≤
        C*(n:ℝ)^4*Real.exp ((n:ℝ)*φ q))
    (hjet : ∀ y ∈ sphericalExceptionalInChart φ n,
      1/(n:ℝ)^110 ≤ ‖realWaveJet n (sphericalChartWeight φ n y)
        (((roundPower sourceAxisOne sourceAxisTwo n ∘
          (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) y‖) :
    ∀ q : Sphere 3, sphericalWeight φ n q/(n:ℝ)^110 ≤
      |(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q|+
      Real.sqrt (coordinateGradientPair g
        (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u)
        (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q)/(n:ℝ) := by
  sorry

end

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end
