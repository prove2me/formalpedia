-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_compact_metric_packet_sign_gain
-- name    : OAI.YauCounterexamples.compact_metric_packet_sign_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:01:10.479409+00:00
-- url     : https://prove2.me/theorems/5e6caf18-3a83-459e-a512-e135a52e3c15
-- title:
--   OAI.YauCounterexamples.compact_metric_packet_sign_gain: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.compact_metric_packet_sign_gain` of [lean/OAI/Geometry/SmoothYau/Limits/CompactMetricPacketSignGain.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CompactMetricPacketSignGain.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology ContDiff ENNReal RealInnerProductSpace`):
--
--   ```lean
--   theorem compact_metric_packet_sign_gain
--       (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       {K : Set NormalWaveSpace} (hK : IsCompact K) :
--       ∃ ε > 0, ε ≤ 1 ∧ ∃ p > 0,
--       ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ → ∃ c₀ > 0,
--       ∀ T c M rₑ Q : ℝ, 0 < T → 0 < c → 0 < M → 0 < rₑ → 0 < Q →
--       ∃ N : ℝ, 2 ≤ N ∧ ∀ t : ℝ, N ≤ t → ∀ (I : Type) [Fintype I] [DecidableEq I]
--         (q : I → NormalWaveParameter) (z : I → Fin 3 → ℂ)
--         (U : I → NormalWaveSpace → ℂ) (b : NormalWaveSpace → ℝ),
--         (Fintype.card I : ℝ) ≤ Q*(t^4)^3 →
--         (∀ i, q i ∈ metricFrameSet g K) →
--         (∀ i, (∑ j, z i j*z i j = -1) ∧
--           ‖phaseRealVector (z i)-gradient (normalWaveProfile g φ (q i)) 0‖ ≤ (Real.sqrt (t^4))⁻¹) →
--         (∀ y ∈ K, ∃ i, t^4*‖y-(q i).1‖ ≤ 1) →
--         (∀ i, U i (q i).1 = Complex.exp (((t^4 : ℝ) : ℂ)*(φ (q i).1 : ℂ))) →
--         (∀ i y, ‖U i y‖ ≤ T*Real.exp (t^4*φ y)*Real.exp (-c*t^4*‖y-(q i).1‖^2)) →
--         (∀ i (r : ℝ), 0 ≤ r → r < rₑ → (Real.sqrt (t^4))⁻¹ ≤ r →
--           ∀ x y : NormalWaveSpace, ‖x-(q i).1‖ ≤ r → ‖y-(q i).1‖ ≤ r → t^4*‖y-x‖ ≤ 1 →
--           ‖U i y-(Real.exp (t^4*fderiv ℝ φ x (y-x)) : ℂ)*
--             Complex.exp (((t^4*normalImagCovector (q i) (z i) (y-x) : ℝ) : ℂ)*Complex.I)*U i x‖ ≤
--           (M*r)*‖(Real.exp (t^4*fderiv ℝ φ x (y-x)) : ℂ)*
--             Complex.exp (((t^4*normalImagCovector (q i) (z i) (y-x) : ℝ) : ℂ)*Complex.I)*U i x‖) →
--         (∀ y ∈ K, |b y| ≤ c₀*Real.exp (t^4*φ y)) →
--         ∀ x ∈ K, ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
--         (∀ j, packetAxisShift x (t^4) ε ℓ j ∈ K) →
--         ∃ j, ENNReal.ofReal p ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
--           {γ | (b x+complexGaussianRealValue (fun i => U i x) γ)*
--             (b (packetAxisShift x (t^4) ε ℓ j)+
--               complexGaussianRealValue (fun i => U i (packetAxisShift x (t^4) ε ℓ j)) γ) < 0}
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveParameter`, `OAI.YauCounterexamples.NormalWaveSpace` and `OAI.YauCounterexamples.PhaseSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.complexGaussianRealValue` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.metricFrameSet`, `OAI.YauCounterexamples.normalImagCovector`, `OAI.YauCounterexamples.normalWaveProfile` and `OAI.YauCounterexamples.packetAxisShift` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.phaseRealVector` and `OAI.YauCounterexamples.profileFrequencyScale` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.compact_actual_waves_sign_and_jets_supported` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CompactMetricPacketSignGain.lean (declaration OAI.YauCounterexamples.compact_metric_packet_sign_gain)

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
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace YauCounterexamples

theorem compact_metric_packet_sign_gain
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ → ∃ c₀ > 0,
    ∀ T c M rₑ Q : ℝ, 0 < T → 0 < c → 0 < M → 0 < rₑ → 0 < Q →
    ∃ N : ℝ, 2 ≤ N ∧ ∀ t : ℝ, N ≤ t → ∀ (I : Type) [Fintype I] [DecidableEq I]
      (q : I → NormalWaveParameter) (z : I → Fin 3 → ℂ)
      (U : I → NormalWaveSpace → ℂ) (b : NormalWaveSpace → ℝ),
      (Fintype.card I : ℝ) ≤ Q*(t^4)^3 →
      (∀ i, q i ∈ metricFrameSet g K) →
      (∀ i, (∑ j, z i j*z i j = -1) ∧
        ‖phaseRealVector (z i)-gradient (normalWaveProfile g φ (q i)) 0‖ ≤ (Real.sqrt (t^4))⁻¹) →
      (∀ y ∈ K, ∃ i, t^4*‖y-(q i).1‖ ≤ 1) →
      (∀ i, U i (q i).1 = Complex.exp (((t^4 : ℝ) : ℂ)*(φ (q i).1 : ℂ))) →
      (∀ i y, ‖U i y‖ ≤ T*Real.exp (t^4*φ y)*Real.exp (-c*t^4*‖y-(q i).1‖^2)) →
      (∀ i (r : ℝ), 0 ≤ r → r < rₑ → (Real.sqrt (t^4))⁻¹ ≤ r →
        ∀ x y : NormalWaveSpace, ‖x-(q i).1‖ ≤ r → ‖y-(q i).1‖ ≤ r → t^4*‖y-x‖ ≤ 1 →
        ‖U i y-(Real.exp (t^4*fderiv ℝ φ x (y-x)) : ℂ)*
          Complex.exp (((t^4*normalImagCovector (q i) (z i) (y-x) : ℝ) : ℂ)*Complex.I)*U i x‖ ≤
        (M*r)*‖(Real.exp (t^4*fderiv ℝ φ x (y-x)) : ℂ)*
          Complex.exp (((t^4*normalImagCovector (q i) (z i) (y-x) : ℝ) : ℂ)*Complex.I)*U i x‖) →
      (∀ y ∈ K, |b y| ≤ c₀*Real.exp (t^4*φ y)) →
      ∀ x ∈ K, ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
      (∀ j, packetAxisShift x (t^4) ε ℓ j ∈ K) →
      ∃ j, ENNReal.ofReal p ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (b x+complexGaussianRealValue (fun i => U i x) γ)*
          (b (packetAxisShift x (t^4) ε ℓ j)+
            complexGaussianRealValue (fun i => U i (packetAxisShift x (t^4) ε ℓ j)) γ) < 0} := by
  sorry
end YauCounterexamples
end

end OAI
end
