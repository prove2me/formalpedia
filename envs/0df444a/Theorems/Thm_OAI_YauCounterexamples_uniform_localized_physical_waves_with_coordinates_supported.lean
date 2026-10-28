-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_uniform_localized_physical_waves_with_coordinates_supported
-- name    : OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:15:26.922279+00:00
-- url     : https://prove2.me/theorems/53d6ecbe-f157-4288-9aaf-59894ae74163
-- title:
--   OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported` of [lean/OAI/Geometry/SmoothYau/Geometry/UniformCoordinatePacketsCommonSlope2.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/UniformCoordinatePacketsCommonSlope2.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Matrix MeasureTheory ProbabilityTheory`, `open scoped Topology ContDiff ENNReal RealInnerProductSpace Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem uniform_localized_physical_waves_with_coordinates_supported (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
--       {K : Set NormalWaveSpace} (hK : IsCompact K)
--       {V : Set NormalWaveSpace} (hV : IsOpen V) (hKV : K ⊆ V)
--       :
--       ∃ (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
--         (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
--         (e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace),
--         ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ b ∧
--         (∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0) ∧
--         (∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0) ∧
--         (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
--           normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
--       ∀ (B C : ℝ) {κ : ℝ}, 0 < κ → ∀ m D : ℕ,
--       ∃ ρ > 0,
--         (∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < ρ → normalWaveEquiv x ∈ (e q).source) ∧
--         ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
--         tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
--         ∃ U : NormalWaveParameter → (Fin 3 → ℂ) → ComplexPhaseMatrix → ℝ → NormalWaveSpace → ℂ,
--         ∃ T > 0, ∃ c > 0,
--           (∀ q ∈ metricFrameSet g K, ∀ z Q n, tsupport (U q z Q n) ⊆ V) ∧
--           (∀ q z Q n x, normalWaveEquiv x ∈ (e q).source →
--             U q z Q n (e q (normalWaveEquiv x)) = normalFamilyWave g φ A b q z Q ζ m D n x) ∧
--           ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix),
--           ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
--           PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
--           ∀ n : ℝ, 1 ≤ n →
--           ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
--           ContDiff ℝ ∞ (U q z Q n) ∧ HasCompactSupport (U q z Q n) ∧
--           U q z Q n q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) ∧
--           ∀ y : NormalWaveSpace, ∀ k ≤ m,
--             ‖iteratedFDeriv ℝ k (U q z Q n) y‖ ≤
--               T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2) ∧
--             ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q z Q n) w +
--               (n : ℂ)*((n : ℂ)+2)*U q z Q n w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ComplexPhaseMatrix`, `OAI.YauCounterexamples.NormalWaveParameter`, `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.PhaseSpace`, `OAI.YauCounterexamples.complexLaplaceBeltrami`, `OAI.YauCounterexamples.metricChristoffel` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.normalJetMap` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.PhaseMatrixValid` and `OAI.YauCounterexamples.actualHessianForm` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.metricFrameSet`, `OAI.YauCounterexamples.normalFamilyWave` and `OAI.YauCounterexamples.normalWaveProfile` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.phaseRealVector` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_uniform_coordinate_packets_common_slope_supported` and `OAI.YauCounterexamples.uniform_coordinate_packets_with_endpoint_ratios_supported` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/UniformCoordinatePacketsCommonSlope2.lean (declaration OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported)

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
namespace YauCounterexamples
section
open Set Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
theorem uniform_localized_physical_waves_with_coordinates_supported (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {V : Set NormalWaveSpace} (hV : IsOpen V) (hKV : K ⊆ V)
    :
    ∃ (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
      (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
      (e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace),
      ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ b ∧
      (∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0) ∧
      (∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0) ∧
      (∀ q, (e q : NormalWaveSpace → NormalWaveSpace) =
        normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
    ∀ (B C : ℝ) {κ : ℝ}, 0 < κ → ∀ m D : ℕ,
    ∃ ρ > 0,
      (∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < ρ → normalWaveEquiv x ∈ (e q).source) ∧
      ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ U : NormalWaveParameter → (Fin 3 → ℂ) → ComplexPhaseMatrix → ℝ → NormalWaveSpace → ℂ,
      ∃ T > 0, ∃ c > 0,
        (∀ q ∈ metricFrameSet g K, ∀ z Q n, tsupport (U q z Q n) ⊆ V) ∧
        (∀ q z Q n x, normalWaveEquiv x ∈ (e q).source →
          U q z Q n (e q (normalWaveEquiv x)) = normalFamilyWave g φ A b q z Q ζ m D n x) ∧
        ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix),
        ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
        ∀ n : ℝ, 1 ≤ n →
        ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
        ContDiff ℝ ∞ (U q z Q n) ∧ HasCompactSupport (U q z Q n) ∧
        U q z Q n q.1 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) ∧
        ∀ y : NormalWaveSpace, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k (U q z Q n) y‖ ≤
            T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q z Q n) w +
            (n : ℂ)*((n : ℂ)+2)*U q z Q n w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y) := by
  sorry
end

open Set Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal RealInnerProductSpace Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end
