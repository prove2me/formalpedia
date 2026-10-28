-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_actual_preparation_on_compact_patch
-- name    : OAI.YauCounterexamples.actual_preparation_on_compact_patch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:56:59.050839+00:00
-- url     : https://prove2.me/theorems/c2c9b250-6701-4baa-ab8b-4c859afa8e84
-- title:
--   OAI.YauCounterexamples.actual_preparation_on_compact_patch: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.actual_preparation_on_compact_patch` of [lean/OAI/Geometry/SmoothYau/Limits/OscDualNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/OscDualNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Metric`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   theorem actual_preparation_on_compact_patch (g : SmoothMetric E E)
--       {u χ s : E → ℝ} (hu : ContDiff ℝ ∞ u) (hχ : ContDiff ℝ ∞ χ) (hs : ContDiff ℝ ∞ s)
--       {K : Set E} (hK : IsCompact K) (C : ℝ) (hC : 0 < C)
--       (hcut : ∀ x ∈ K, 0 ≤ χ x ∧ χ x ≤ 1)
--       (hq : ∀ x ∈ K, (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0)
--       (hstrict : ∀ x ∈ K, ∀ c ∈ Icc (-2*C) (2*C), quadraticPlaneStrict
--         (metricProfileTraceForm (selfMetricFlat g x)
--           (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
--           (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)))
--       (hfull : ∀ x ∈ K, ∀ c ∈ Icc C (2*C), quadraticPlaneFull
--         (metricProfileTraceForm (selfMetricFlat g x)
--           (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
--           (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)))
--       (ε : ℝ) (hε : 0 < ε) :
--       ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ τ : ℝ, ∀ x ∈ K,
--         let u' := preparationCorrugation u χ preparationWave s C N τ
--         coordinateMetricGradient g u' x ≠ 0 ∧ actualProfileStrict g u' x ∧
--         (χ x = 1 → 1 < preparationWaveSecond (N*s x+τ) → actualProfileFull g u' x) ∧
--         |u' x-u x| < ε ∧ ‖fderiv ℝ u' x-fderiv ℝ u x‖ < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CoordinateForm`, `OAI.YauCounterexamples.ProfileForm`, `OAI.YauCounterexamples.actualCoordinateHessian` and `OAI.YauCounterexamples.selfMetricFlat` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.preparationCorrugation`, `OAI.YauCounterexamples.preparationWave` and `OAI.YauCounterexamples.preparationWaveSecond` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.coordinateMetricGradient` and `OAI.YauCounterexamples.metricProfileTraceForm` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.profileRankOne`, `OAI.YauCounterexamples.quadraticPlaneFull` and `OAI.YauCounterexamples.quadraticPlaneStrict` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.actualProfileFull` and `OAI.YauCounterexamples.actualProfileStrict` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_actual_metric_preparation` and `OAI.YauCounterexamples.actual_metric_profile_cycle` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/OscDualNorm.lean (declaration OAI.YauCounterexamples.actual_preparation_on_compact_patch)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009

section

attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem actual_preparation_on_compact_patch (g : SmoothMetric E E)
    {u χ s : E → ℝ} (hu : ContDiff ℝ ∞ u) (hχ : ContDiff ℝ ∞ χ) (hs : ContDiff ℝ ∞ s)
    {K : Set E} (hK : IsCompact K) (C : ℝ) (hC : 0 < C)
    (hcut : ∀ x ∈ K, 0 ≤ χ x ∧ χ x ≤ 1)
    (hq : ∀ x ∈ K, (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0)
    (hstrict : ∀ x ∈ K, ∀ c ∈ Icc (-2*C) (2*C), quadraticPlaneStrict
      (metricProfileTraceForm (selfMetricFlat g x)
        (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
        (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)))
    (hfull : ∀ x ∈ K, ∀ c ∈ Icc C (2*C), quadraticPlaneFull
      (metricProfileTraceForm (selfMetricFlat g x)
        (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
        (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ τ : ℝ, ∀ x ∈ K,
      let u' := preparationCorrugation u χ preparationWave s C N τ
      coordinateMetricGradient g u' x ≠ 0 ∧ actualProfileStrict g u' x ∧
      (χ x = 1 → 1 < preparationWaveSecond (N*s x+τ) → actualProfileFull g u' x) ∧
      |u' x-u x| < ε ∧ ‖fderiv ℝ u' x-fderiv ℝ u x‖ < ε := by
  sorry

end
end YauCounterexamples

end OAI
end
