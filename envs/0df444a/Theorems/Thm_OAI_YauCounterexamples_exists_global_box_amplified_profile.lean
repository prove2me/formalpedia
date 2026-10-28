-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_exists_global_box_amplified_profile
-- name    : OAI.YauCounterexamples.exists_global_box_amplified_profile
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:01:51.194652+00:00
-- url     : https://prove2.me/theorems/72b10590-f3d3-4f16-8a78-a7a427597135
-- title:
--   OAI.YauCounterexamples.exists_global_box_amplified_profile: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.exists_global_box_amplified_profile` of [lean/OAI/Geometry/SmoothYau/Geometry/ExistsGlobalBoxAmplifiedProfile.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ExistsGlobalBoxAmplifiedProfile.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter MeasureTheory BoxIntegral`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   theorem exists_global_box_amplified_profile
--       (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       {K : Set NormalWaveSpace} (I : Box (Fin 3))
--       {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
--       (hnc : ∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x)
--       (hcrit : ∀ x ∈ K, fderiv ℝ φ x = 0 →
--         ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
--           ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v)
--       (hIK : normalWaveEquiv '' Box.Icc I ⊆ K)
--       (ha : ∀ x ∈ normalWaveEquiv '' Box.Icc I, coordinateMetricGradient g φ x ≠ 0)
--       (T : ℝ) {η : ℝ} (hη : 0 < η) :
--       ∃ ψ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ ψ ∧
--         HasCompactSupport (fun x => ψ x-φ x) ∧
--         tsupport (fun x => ψ x-φ x) ⊆ normalWaveEquiv '' Box.Ioo I ∧
--         (∀ x, |ψ x-φ x| < η) ∧
--         (∀ x ∈ normalWaveEquiv '' Box.Icc I,
--           coordinateMetricGradient g ψ x ≠ 0 ∧ actualProfileStrict g ψ x) ∧
--         (∀ x ∈ K, fderiv ℝ ψ x ≠ 0 → actualProfileStrict g ψ x) ∧
--         (∀ x ∈ K, fderiv ℝ ψ x = 0 →
--           ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
--             ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g ψ x v v) ∧
--         T < ∫ x in Box.Icc I, profileFrequencyScale g ψ (normalWaveEquiv x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CoordinateForm`, `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.actualCoordinateHessian` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.coordinateMetricGradient` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.actualProfileStrict` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.profileFrequencyScale` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_global_spherical_wave_profile` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ExistsGlobalBoxAmplifiedProfile.lean (declaration OAI.YauCounterexamples.exists_global_box_amplified_profile)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010

section

attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

theorem exists_global_box_amplified_profile
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (I : Box (Fin 3))
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hnc : ∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x)
    (hcrit : ∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v)
    (hIK : normalWaveEquiv '' Box.Icc I ⊆ K)
    (ha : ∀ x ∈ normalWaveEquiv '' Box.Icc I, coordinateMetricGradient g φ x ≠ 0)
    (T : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ψ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ ψ ∧
      HasCompactSupport (fun x => ψ x-φ x) ∧
      tsupport (fun x => ψ x-φ x) ⊆ normalWaveEquiv '' Box.Ioo I ∧
      (∀ x, |ψ x-φ x| < η) ∧
      (∀ x ∈ normalWaveEquiv '' Box.Icc I,
        coordinateMetricGradient g ψ x ≠ 0 ∧ actualProfileStrict g ψ x) ∧
      (∀ x ∈ K, fderiv ℝ ψ x ≠ 0 → actualProfileStrict g ψ x) ∧
      (∀ x ∈ K, fderiv ℝ ψ x = 0 →
        ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
          ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g ψ x v v) ∧
      T < ∫ x in Box.Icc I, profileFrequencyScale g ψ (normalWaveEquiv x) := by
  sorry

end YauCounterexamples
end

end OAI
end
