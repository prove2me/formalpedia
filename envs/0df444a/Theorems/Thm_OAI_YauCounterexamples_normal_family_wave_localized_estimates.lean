-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_normal_family_wave_localized_estimates
-- name    : OAI.YauCounterexamples.normal_family_wave_localized_estimates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:10:34.23393+00:00
-- url     : https://prove2.me/theorems/3a9d7532-4228-4416-9346-12f74c6f9a20
-- title:
--   OAI.YauCounterexamples.normal_family_wave_localized_estimates: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.normal_family_wave_localized_estimates` of [lean/OAI/Geometry/SmoothYau/Estimates/NormalFamilyWaveLocalizedEstimates.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/NormalFamilyWaveLocalizedEstimates.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Matrix`, `open scoped Topology ContDiff Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem normal_family_wave_localized_estimates (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
--       {K : Set NormalWaveSpace} (hK : IsCompact K)
--       (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
--       (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
--       (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
--       (hA0 : ∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0)
--       (hAd : ∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
--       (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
--       ∃ r : ℝ, 0 < r ∧ ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
--         ∃ T : ℝ, 0 < T ∧ ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix), ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
--           PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
--           ∀ n : ℝ, 1 ≤ n →
--           ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
--           ∀ x ∈ Metric.ball (0 : Fin 3 → ℝ) r, ∀ k ≤ m,
--             ‖iteratedFDeriv ℝ k (normalFamilyWave g φ A b q z Q ζ m D n) x‖ ≤
--                 T*n^k*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x))*
--                   Real.exp (-(κ/2)*n*‖x‖^2) ∧
--             ‖iteratedFDeriv ℝ k (fun y =>
--               waveCoordinateOperator (fun i => Pi.single i 1)
--                 (fun i j y => A (q,y) i j) (fun j y => b (q,y) j)
--                 (normalFamilyWave g φ A b q z Q ζ m D n) y +
--               (n : ℂ)*((n : ℂ)+2)*normalFamilyWave g φ A b q z Q ζ m D n y) x‖ ≤
--                 T*(n^(D+1))⁻¹*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ComplexPhaseMatrix`, `OAI.YauCounterexamples.NormalWaveParameter`, `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.PhaseSpace` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.PhaseMatrixValid` and `OAI.YauCounterexamples.actualHessianForm` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.metricFrameSet`, `OAI.YauCounterexamples.normalFamilyWave`, `OAI.YauCounterexamples.normalWaveProfile` and `OAI.YauCounterexamples.waveCoordinateOperator` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.phaseRealVector` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/NormalFamilyWaveLocalizedEstimates.lean (declaration OAI.YauCounterexamples.normal_family_wave_localized_estimates)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section

attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
theorem normal_family_wave_localized_estimates (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
    (hA0 : ∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0)
    (hAd : ∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ T : ℝ, 0 < T ∧ ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix), ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
        ∀ n : ℝ, 1 ≤ n →
        ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
        ∀ x ∈ Metric.ball (0 : Fin 3 → ℝ) r, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k (normalFamilyWave g φ A b q z Q ζ m D n) x‖ ≤
              T*n^k*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x))*
                Real.exp (-(κ/2)*n*‖x‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun y =>
            waveCoordinateOperator (fun i => Pi.single i 1)
              (fun i j y => A (q,y) i j) (fun j y => b (q,y) j)
              (normalFamilyWave g φ A b q z Q ζ m D n) y +
            (n : ℂ)*((n : ℂ)+2)*normalFamilyWave g φ A b q z Q ζ m D n y) x‖ ≤
              T*(n^(D+1))⁻¹*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x)) := by
  sorry
end YauCounterexamples
end

end OAI
end
