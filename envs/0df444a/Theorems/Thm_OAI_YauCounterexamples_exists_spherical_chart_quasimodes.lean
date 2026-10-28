-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_spherical_chart_quasimodes
-- name    : OAI.YauCounterexamples.exists_spherical_chart_quasimodes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:38:32.227438+00:00
-- url     : https://prove2.me/theorems/abdbca72-448e-4dd9-b00e-5692e11d9cd0
-- title:
--   OAI.YauCounterexamples.exists_spherical_chart_quasimodes: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_spherical_chart_quasimodes` of [lean/OAI/Geometry/SmoothYau/DifferentialEq/ExistsSphericalGlobalQuasimodes.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/DifferentialEq/ExistsSphericalGlobalQuasimodes.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter Metric`, `open scoped Topology InnerProductSpace`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Manifold`, `open scoped Topology ContDiff`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ENNReal NNReal`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter Metric`, `open scoped Topology InnerProductSpace`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Manifold Metric MeasureTheory BoxIntegral`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   theorem exists_spherical_chart_quasimodes
--       (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
--       {t s r : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r) (hr : r < 3/10)
--       (A : ℝ) :
--       ∃ φ : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ ∧
--         (∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
--           sphericalRadius sourceAxisOne sourceAxisTwo q < t →
--           Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q) ∧
--         (∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
--           φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) ∧
--         ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
--           (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
--         ∀ m D : ℕ, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
--           ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
--             tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
--               ((chartAt (Euclidean 3) sourcePole).symm y) < r} ∧
--             (∀ x : NormalWaveSpace, ∀ j ≤ m,
--               ‖iteratedFDeriv ℝ j u x‖ ≤ C*(n:ℝ)^(j+4)*
--                 Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm x)) ∧
--               ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (sphereChartMetric g sourcePole) u y+
--                   (n:ℝ)*(n+2)*u y) x‖ ≤ C*((n:ℝ)^(D+1))⁻¹*
--                 Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm x))) ∧
--             (∀ y ∈ sphericalExceptionalInChart φ n,
--               1/(n:ℝ)^110 ≤ ‖realWaveJet n (sphericalChartWeight φ n y)
--                 (((roundPower sourceAxisOne sourceAxisTwo n ∘
--                   (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) y‖) ∧
--             ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
--               (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
--               (fun a => ε/((n:ℝ)*ℓ a.val))
--               (((roundPower sourceAxisOne sourceAxisTwo n ∘
--                 (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) ∧
--             ENNReal.ofReal (A*(n:ℝ)) < 36*Measure.hausdorffMeasure 2
--               ((⋃ a : {J : Box (Fin 3) // J ∈ partition.boxes}, Box.Ioo a.val) ∩
--                 {x | ((roundPower sourceAxisOne sourceAxisTwo n ∘
--                   (chartAt (Euclidean 3) sourcePole).symm)+u) (normalWaveEquiv x)=0})
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.normalWaveEquiv`, `OAI.YauCounterexamples.sourceAxisOne`, `OAI.YauCounterexamples.sourceAxisTwo`, `OAI.YauCounterexamples.sourcePole`, `OAI.YauCounterexamples.sourceSignBox`, `OAI.YauCounterexamples.sphericalRadius` and `OAI.YauCounterexamples.SignTests.signCertificate` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.realWaveJet` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.sphereChartMetric` and `OAI.YauCounterexamples.sphericalProfileMetricNeighborhood` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.roundPower`, `OAI.YauCounterexamples.sphericalChartWeight` and `OAI.YauCounterexamples.sphericalExceptionalInChart` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_global_quasimodes` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/DifferentialEq/ExistsSphericalGlobalQuasimodes.lean (declaration OAI.YauCounterexamples.exists_spherical_chart_quasimodes)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

theorem exists_spherical_chart_quasimodes
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {t s r : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r) (hr : r < 3/10)
    (A : ℝ) :
    ∃ φ : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ ∧
      (∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
        sphericalRadius sourceAxisOne sourceAxisTwo q < t →
        Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q) ∧
      (∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
        φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) ∧
      ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
        (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
      ∀ m D : ℕ, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
          tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
            ((chartAt (Euclidean 3) sourcePole).symm y) < r} ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*(n:ℝ)^(j+4)*
              Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm x)) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (sphereChartMetric g sourcePole) u y+
                (n:ℝ)*(n+2)*u y) x‖ ≤ C*((n:ℝ)^(D+1))⁻¹*
              Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm x))) ∧
          (∀ y ∈ sphericalExceptionalInChart φ n,
            1/(n:ℝ)^110 ≤ ‖realWaveJet n (sphericalChartWeight φ n y)
              (((roundPower sourceAxisOne sourceAxisTwo n ∘
                (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) y‖) ∧
          ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
            (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
            (fun a => ε/((n:ℝ)*ℓ a.val))
            (((roundPower sourceAxisOne sourceAxisTwo n ∘
              (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) ∧
          ENNReal.ofReal (A*(n:ℝ)) < 36*Measure.hausdorffMeasure 2
            ((⋃ a : {J : Box (Fin 3) // J ∈ partition.boxes}, Box.Ioo a.val) ∩
              {x | ((roundPower sourceAxisOne sourceAxisTwo n ∘
                (chartAt (Euclidean 3) sourcePole).symm)+u) (normalWaveEquiv x)=0}) := by
  sorry

end

open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

end YauCounterexamples
end

end OAI
end
