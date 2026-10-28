-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_actual_metric_profile_cycle
-- name    : OAI.YauCounterexamples.actual_metric_profile_cycle
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:56:04.234105+00:00
-- url     : https://prove2.me/theorems/e2ab8357-2767-421f-9aa7-b859bd61b99f
-- title:
--   OAI.YauCounterexamples.actual_metric_profile_cycle: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.actual_metric_profile_cycle` of [lean/OAI/Geometry/SmoothYau/Geometry/ActualProfileCycleGain.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ActualProfileCycleGain.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set MeasureTheory Filter`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped Topology ENNReal ContDiff`):
--
--   ```lean
--   theorem actual_metric_profile_cycle (hdim : Module.finrank ℝ E = 3)
--       (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
--       {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
--       (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g u x ≠ 0)
--       (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g u x)
--       (μ : Measure E) [IsLocallyFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
--       ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport (fun x => v x-u x) ∧
--         tsupport (fun x => v x-u x) ⊆ Ω ∧ (∀ x, |v x-u x| < ε) ∧
--         (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x) ∧
--         (1+actualProfileCycleGain)*actualProfileMass g u μ Ω ≤ actualProfileMass g v μ Ω
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.coordinateMetricGradient` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.actualProfileCycleGain`, `OAI.YauCounterexamples.actualProfileMass` and `OAI.YauCounterexamples.actualProfileStrict` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.exists_global_box_amplified_profile` and `OAI.YauCounterexamples.exists_three_robust_global_profile_family` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ActualProfileCycleGain.lean (declaration OAI.YauCounterexamples.actual_metric_profile_cycle)

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

noncomputable section
namespace YauCounterexamples

open Set MeasureTheory Filter
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem actual_metric_profile_cycle (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g u x ≠ 0)
    (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g u x)
    (μ : Measure E) [IsLocallyFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport (fun x => v x-u x) ∧
      tsupport (fun x => v x-u x) ⊆ Ω ∧ (∀ x, |v x-u x| < ε) ∧
      (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x) ∧
      (1+actualProfileCycleGain)*actualProfileMass g u μ Ω ≤ actualProfileMass g v μ Ω := by
  sorry

end YauCounterexamples
end

end OAI
end
