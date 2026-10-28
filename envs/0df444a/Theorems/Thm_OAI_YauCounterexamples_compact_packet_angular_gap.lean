-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_compact_packet_angular_gap
-- name    : OAI.YauCounterexamples.compact_packet_angular_gap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:02:25.502607+00:00
-- url     : https://prove2.me/theorems/9e483474-e0c2-41a6-96ed-9b968ec04148
-- title:
--   OAI.YauCounterexamples.compact_packet_angular_gap: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.compact_packet_angular_gap` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ScaledThreeAxisEnergy.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ScaledThreeAxisEnergy.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff RealInnerProductSpace`):
--
--   ```lean
--   theorem compact_packet_angular_gap (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       {K : Set NormalWaveSpace} (hK : IsCompact K) :
--       ∃ ε > 0, ε ≤ 1 ∧ ∃ κ > 0, κ ≤ 1 ∧
--         ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
--         ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ z : Fin 3 → ℂ, ∀ x : NormalWaveSpace,
--           (∑ i, z i*z i = -1) → ‖x-q.1‖ ≤ r →
--           ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ r →
--           ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
--           let θ := fun i => ε/ℓ*normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i)
--           (∀ i, |θ i| ≤ 1) ∧ κ ≤ ∑ i, (θ i)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` and `OAI.YauCounterexamples.PhaseSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.metricFrameSet`, `OAI.YauCounterexamples.normalImagCovector` and `OAI.YauCounterexamples.normalWaveProfile` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.phaseRealVector` and `OAI.YauCounterexamples.profileFrequencyScale` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.compact_metric_packet_sign_gain` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ScaledThreeAxisEnergy.lean (declaration OAI.YauCounterexamples.compact_packet_angular_gap)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section

attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

theorem compact_packet_angular_gap (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ κ > 0, κ ≤ 1 ∧
      ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
      ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ z : Fin 3 → ℂ, ∀ x : NormalWaveSpace,
        (∑ i, z i*z i = -1) → ‖x-q.1‖ ≤ r →
        ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ r →
        ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
        let θ := fun i => ε/ℓ*normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (∀ i, |θ i| ≤ 1) ∧ κ ≤ ∑ i, (θ i)^2 := by
  sorry
end YauCounterexamples
end

end OAI
end
