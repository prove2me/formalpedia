-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_spherical_pin_near
-- name    : OAI.YauCounterexamples.spherical_pin_near
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:09:57.03901+00:00
-- url     : https://prove2.me/theorems/33bcd7f1-ad96-4be7-9849-856a27c22e7f
-- title:
--   OAI.YauCounterexamples.spherical_pin_near: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.spherical_pin_near` of [lean/OAI/Geometry/SmoothYau/Estimates/SphericalPinFormNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/SphericalPinFormNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral`, `open scoped Topology ContDiff Distributions ENNReal NNReal`):
--
--   ```lean
--   theorem spherical_pin_near
--       (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
--       (g : SmoothMetric (Euclidean 3) (Sphere 3)) {b c : ℝ}
--       (hb0 : 0<b) (hbc : b < c) (hc : c<3/10)
--       (hext : sphericalExterior g₀ g b) (k : ℕ) (hk3 : 3≤k)
--       (u : Sphere 3 → ℝ) (hu : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
--       (hue : ∀ q, -laplaceBeltrami g u q=sphereFrequency k*u q)
--       (hout : ∀ q, b < sphericalRadius sourceAxisOne sourceAxisTwo q → u q=roundPower sourceAxisOne sourceAxisTwo k q)
--       (U : Set SphericalTensor) (hU : IsOpen U)
--       (hgU : sphericalTensorOf g₀ g (sphericalExterior_mono (hbc.trans hc).le hext) ∈ U) :
--       ∃ h : SmoothMetric (Euclidean 3) (Sphere 3), ∃ he : sphericalExterior g₀ h c,
--         sphericalTensorOf g₀ h (sphericalExterior_mono hc.le he) ∈ U ∧
--         (∀ q, -laplaceBeltrami h u q=sphereFrequency k*u q) ∧
--         SphericalSimple h u (sphereFrequency k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.MetricForm`, `OAI.YauCounterexamples.sourceAxisOne`, `OAI.YauCounterexamples.sourceAxisTwo` and `OAI.YauCounterexamples.sphericalRadius` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.sphereFrequency` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.SphericalSimple`, `OAI.YauCounterexamples.SphericalTensor`, `OAI.YauCounterexamples.sphericalAmbientFormNorm`, `OAI.YauCounterexamples.sphericalAmbientFormSpace` and `OAI.YauCounterexamples.sphericalTensorSupport` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.roundPower` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.sphericalExterior` and `OAI.YauCounterexamples.sphericalExterior_mono` (definitions bundle `OAIQ070A008` of this split); `OAI.YauCounterexamples.sphericalTensorOf` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.Euclidean`, `OAI.YauCounterexamples.IsRound`, `OAI.YauCounterexamples.SmoothMetric`, `OAI.YauCounterexamples.Sphere` and `OAI.YauCounterexamples.laplaceBeltrami` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_spherical_simple_stage` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/SphericalPinFormNorm.lean (declaration OAI.YauCounterexamples.spherical_pin_near)

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

open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
local instance sphericalPinFormNorm_re45ecf_1 : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalPinFormSpace_re45ecf_1 : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
theorem spherical_pin_near
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) {b c : ℝ}
    (hb0 : 0<b) (hbc : b < c) (hc : c<3/10)
    (hext : sphericalExterior g₀ g b) (k : ℕ) (hk3 : 3≤k)
    (u : Sphere 3 → ℝ) (hu : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
    (hue : ∀ q, -laplaceBeltrami g u q=sphereFrequency k*u q)
    (hout : ∀ q, b < sphericalRadius sourceAxisOne sourceAxisTwo q → u q=roundPower sourceAxisOne sourceAxisTwo k q)
    (U : Set SphericalTensor) (hU : IsOpen U)
    (hgU : sphericalTensorOf g₀ g (sphericalExterior_mono (hbc.trans hc).le hext) ∈ U) :
    ∃ h : SmoothMetric (Euclidean 3) (Sphere 3), ∃ he : sphericalExterior g₀ h c,
      sphericalTensorOf g₀ h (sphericalExterior_mono hc.le he) ∈ U ∧
      (∀ q, -laplaceBeltrami h u q=sphereFrequency k*u q) ∧
      SphericalSimple h u (sphereFrequency k) := by
  sorry

end YauCounterexamples
end

end OAI
end
