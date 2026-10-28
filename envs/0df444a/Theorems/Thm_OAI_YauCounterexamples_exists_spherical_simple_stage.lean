-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_spherical_simple_stage
-- name    : OAI.YauCounterexamples.exists_spherical_simple_stage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:03:07.072125+00:00
-- url     : https://prove2.me/theorems/ee292050-a5ae-4e5b-bcb7-01c7fbf3b6bf
-- title:
--   OAI.YauCounterexamples.exists_spherical_simple_stage: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_spherical_simple_stage` of [lean/OAI/Geometry/SmoothYau/Limits/SphericalFixedFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/SphericalFixedFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral`, `open scoped Topology ContDiff Distributions ENNReal NNReal`):
--
--   ```lean
--   theorem exists_spherical_simple_stage
--       (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
--       {R t s r a b c : ℝ} (hR : (1/5:ℝ) ≤ R) (hRt : R<t) (hts : t < s) (hsr : s < r)
--       (hra : r<a) (hab : a<b) (hbc : b < c) (hc : c<3/10)
--       (hext : sphericalExterior g₀ g R)
--       (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
--         ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
--       (A : ℝ) (M : ℕ) (U : Set SphericalTensor) (hU : IsOpen U)
--       (hgU : sphericalTensorOf g₀ g (sphericalExterior_mono (by linarith) hext) ∈ U) :
--       ∃ k : ℕ, M ≤ k ∧ 3 ≤ k ∧ ∃ h : SmoothMetric (Euclidean 3) (Sphere 3),
--         ∃ he : sphericalExterior g₀ h c,
--         sphericalTensorOf g₀ h (sphericalExterior_mono hc.le he) ∈ U ∧
--         ∃ u : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
--           (∀ q, -laplaceBeltrami h u q=sphereFrequency k*u q) ∧
--           SphericalRegular u ∧ SphericalSimple h u (sphereFrequency k) ∧
--           SphericalSignAbove u (A*(k:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.MetricForm`, `OAI.YauCounterexamples.SphericalRegular`, `OAI.YauCounterexamples.SphericalSignAbove`, `OAI.YauCounterexamples.selfMetricFlat`, `OAI.YauCounterexamples.sourceAxisOne`, `OAI.YauCounterexamples.sourceAxisTwo`, `OAI.YauCounterexamples.sourcePole` and `OAI.YauCounterexamples.sphericalCoverage` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.sphereFrequency` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.SphericalSimple`, `OAI.YauCounterexamples.SphericalTensor`, `OAI.YauCounterexamples.sphereChartMetric`, `OAI.YauCounterexamples.sphericalAmbientFormNorm`, `OAI.YauCounterexamples.sphericalAmbientFormSpace`, `OAI.YauCounterexamples.sphericalProfileMetricNeighborhood` and `OAI.YauCounterexamples.sphericalTensorSupport` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.sphericalExterior` and `OAI.YauCounterexamples.sphericalExterior_mono` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.sphericalTensorOf` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_fixed_witnesses` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/SphericalFixedFormNorm.lean (declaration OAI.YauCounterexamples.exists_spherical_simple_stage)

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
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

local instance sphericalStageFormNorm_r03f049_1 : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalStageFormSpace_r03f049_1 : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
theorem exists_spherical_simple_stage
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {R t s r a b c : ℝ} (hR : (1/5:ℝ) ≤ R) (hRt : R<t) (hts : t < s) (hsr : s < r)
    (hra : r<a) (hab : a<b) (hbc : b < c) (hc : c<3/10)
    (hext : sphericalExterior g₀ g R)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    (A : ℝ) (M : ℕ) (U : Set SphericalTensor) (hU : IsOpen U)
    (hgU : sphericalTensorOf g₀ g (sphericalExterior_mono (by linarith) hext) ∈ U) :
    ∃ k : ℕ, M ≤ k ∧ 3 ≤ k ∧ ∃ h : SmoothMetric (Euclidean 3) (Sphere 3),
      ∃ he : sphericalExterior g₀ h c,
      sphericalTensorOf g₀ h (sphericalExterior_mono hc.le he) ∈ U ∧
      ∃ u : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
        (∀ q, -laplaceBeltrami h u q=sphereFrequency k*u q) ∧
        SphericalRegular u ∧ SphericalSimple h u (sphereFrequency k) ∧
        SphericalSignAbove u (A*(k:ℝ)) := by
  sorry
end

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end
