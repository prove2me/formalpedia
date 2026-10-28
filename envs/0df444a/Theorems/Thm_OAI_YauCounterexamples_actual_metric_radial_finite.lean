-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_actual_metric_radial_finite
-- name    : OAI.YauCounterexamples.actual_metric_radial_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:56:37.662645+00:00
-- url     : https://prove2.me/theorems/ec3adedb-0641-43e3-9d02-93a047d1f53e
-- title:
--   OAI.YauCounterexamples.actual_metric_radial_finite: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.actual_metric_radial_finite` of [lean/OAI/Geometry/SmoothYau/Geometry/RadialFiniteDualNorm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/RadialFiniteDualNorm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Function Filter Metric MeasureTheory Manifold Bundle`, `open scoped Topology ENNReal InnerProductSpace ContDiff`):
--
--   ```lean
--   theorem actual_metric_radial_finite (hdim : Module.finrank ℝ E = 3)
--       (g : SmoothMetric E E) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
--       {Ω U : Set E} (hU : IsOpen U) (hUΩ : U ⊆ Ω)
--       (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g ψ x ≠ 0)
--       (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g ψ x)
--       (hfull : ∀ x ∈ U, actualProfileFull g ψ x)
--       (μ : Measure E) [IsFiniteMeasure μ]
--       {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
--       (hβ0 : β 0 = 0) (hβv : ∀ t, β t ∈ Icc 0 1)
--       {b r R δ c ε ε₀ : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hR : 2*R < 1)
--       (hb : b ≤ r^2) (hz : ∀ t, b ≤ t → β t = 0)
--       (hδ : 0 < δ) (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε < 1) (hε₀ : 0 < ε₀)
--       (Fmax S Kb : ℝ) (hFmax : 0 < Fmax) (hS : 0 < S) (hKb : 0 < Kb)
--       (hcoef : ∀ z, 0 ≤ periodicRadialSpeed β R z ∧ periodicRadialSpeed β R z ≤ Fmax ∧
--         0 ≤ periodicAngularSecond β R z ∧
--         (periodicRadialSpeed β R z)^2 ≤ S*periodicAngularSecond β R z ∧
--         |periodicRadialSecond β R z| ≤ Kb)
--       (hsmall : 9216*Kb*S*δ^2 ≤ 1)
--       (q : ProfilePlane) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
--       (hwindow : ∀ z, profileTorusQuotient z ∈
--         ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ →
--           c ≤ periodicRadialSpeed β R z) :
--       ∃ (v : E → ℝ) (G : Set E), ContDiff ℝ ∞ v ∧
--         HasCompactSupport (fun x => v x-ψ x) ∧ tsupport (fun x => v x-ψ x) ⊆ U ∧
--         (∀ x, |v x-ψ x| < ε₀) ∧
--         (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
--           (1-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x) ∧
--         MeasurableSet G ∧ G ⊆ U ∧
--         μ U/2 * ENNReal.ofReal ((2*ρ)^2) ≤ μ G ∧
--         ∀ x ∈ G, (Real.sqrt (1+δ^2*c^2/16)-ε)*actualProfileSpeed g ψ x ≤
--           actualProfileSpeed g v x
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ProfilePlane`, `OAI.YauCounterexamples.ProfileTorus`, `OAI.YauCounterexamples.periodicAngularSecond`, `OAI.YauCounterexamples.periodicRadialSecond`, `OAI.YauCounterexamples.periodicRadialSpeed` and `OAI.YauCounterexamples.profileTorusQuotient` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.coordinateMetricGradient` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.actualProfileFull`, `OAI.YauCounterexamples.actualProfileSpeed` and `OAI.YauCounterexamples.actualProfileStrict` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.actual_metric_profile_cycle` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/RadialFiniteDualNorm.lean (declaration OAI.YauCounterexamples.actual_metric_radial_finite)

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

open Set Function Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ENNReal InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem actual_metric_radial_finite (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {Ω U : Set E} (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g ψ x ≠ 0)
    (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g ψ x)
    (hfull : ∀ x ∈ U, actualProfileFull g ψ x)
    (μ : Measure E) [IsFiniteMeasure μ]
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) (hβv : ∀ t, β t ∈ Icc 0 1)
    {b r R δ c ε ε₀ : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hR : 2*R < 1)
    (hb : b ≤ r^2) (hz : ∀ t, b ≤ t → β t = 0)
    (hδ : 0 < δ) (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε < 1) (hε₀ : 0 < ε₀)
    (Fmax S Kb : ℝ) (hFmax : 0 < Fmax) (hS : 0 < S) (hKb : 0 < Kb)
    (hcoef : ∀ z, 0 ≤ periodicRadialSpeed β R z ∧ periodicRadialSpeed β R z ≤ Fmax ∧
      0 ≤ periodicAngularSecond β R z ∧
      (periodicRadialSpeed β R z)^2 ≤ S*periodicAngularSecond β R z ∧
      |periodicRadialSecond β R z| ≤ Kb)
    (hsmall : 9216*Kb*S*δ^2 ≤ 1)
    (q : ProfilePlane) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (hwindow : ∀ z, profileTorusQuotient z ∈
      ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ →
        c ≤ periodicRadialSpeed β R z) :
    ∃ (v : E → ℝ) (G : Set E), ContDiff ℝ ∞ v ∧
      HasCompactSupport (fun x => v x-ψ x) ∧ tsupport (fun x => v x-ψ x) ⊆ U ∧
      (∀ x, |v x-ψ x| < ε₀) ∧
      (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
        (1-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x) ∧
      MeasurableSet G ∧ G ⊆ U ∧
      μ U/2 * ENNReal.ofReal ((2*ρ)^2) ≤ μ G ∧
      ∀ x ∈ G, (Real.sqrt (1+δ^2*c^2/16)-ε)*actualProfileSpeed g ψ x ≤
        actualProfileSpeed g v x := by
  sorry

end
end YauCounterexamples

end OAI
end
