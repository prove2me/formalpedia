-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_physical_finite_superposition_complete_supported
-- name    : OAI.YauCounterexamples.physical_finite_superposition_complete_supported
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:09:29.341113+00:00
-- url     : https://prove2.me/theorems/cd02a2bf-ae0a-4238-9816-304bdc7338d9
-- title:
--   OAI.YauCounterexamples.physical_finite_superposition_complete_supported: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.physical_finite_superposition_complete_supported` of [lean/OAI/Geometry/SmoothYau/Estimates/PhysicalFiniteSuperpositionCompleteSupported.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/PhysicalFiniteSuperpositionCompleteSupported.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   theorem physical_finite_superposition_complete_supported
--       (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
--       {K : Set NormalWaveSpace} (hK : IsCompact K)
--       {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O)
--       (hnc : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 ≠ 0 → ∃ v,
--         inner ℝ (gradient (normalWaveProfile g φ q) 0) v = 0 ∧
--         ‖v‖^2 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 ∧
--         0 < actualHessianForm (normalWaveProfile g φ q) (gradient (normalWaveProfile g φ q) 0)
--           (gradient (normalWaveProfile g φ q) 0)+actualHessianForm (normalWaveProfile g φ q) v v)
--       (hcrit : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 = 0 →
--         ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
--           ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (normalWaveProfile g φ q) v v)
--       (m D : ℕ) :
--       ∃ ρ > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
--         tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
--       ∃ T > 0, ∃ c > 0, ∃ M₀ > 0, ∃ C > 0, ∃ r₀ > 0, ∃ rₑ > 0, ∃ N : ℝ, 1 ≤ N ∧
--         ∀ n : ℝ, N ≤ n →
--         ∃ (z : metricFrameSet g K → Fin 3 → Fin 3 → ℂ)
--           (U : metricFrameSet g K → Fin 3 → NormalWaveSpace → ℂ),
--           (∀ q ℓ, tsupport (U q ℓ) ⊆ O) ∧
--           (∀ q ℓ, (∑ i, z q ℓ i*z q ℓ i = -1) ∧
--             ‖phaseRealVector (z q ℓ)-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
--           (∀ q ℓ, ContDiff ℝ ∞ (U q ℓ) ∧ HasCompactSupport (U q ℓ) ∧
--             U q ℓ q.1.1 = Complex.exp ((n : ℂ)*(φ q.1.1 : ℂ)) ∧
--             ∀ y : NormalWaveSpace, ∀ k ≤ m,
--               ‖iteratedFDeriv ℝ k (U q ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1.1‖^2) ∧
--               ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q ℓ) w +
--                 (n : ℂ)*((n : ℂ)+2)*U q ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
--           (∀ q ℓ (r : ℝ), 0 ≤ r → r < rₑ → (Real.sqrt n)⁻¹ ≤ r →
--             ∀ x y : NormalWaveSpace, ‖x-q.1.1‖ ≤ r → ‖y-q.1.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
--             ‖U q ℓ y-(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
--                 Complex.exp (((n*normalImagCovector q (z q ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U q ℓ x‖ ≤
--             (M₀*r)*‖(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
--                 Complex.exp (((n*normalImagCovector q (z q ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U q ℓ x‖) ∧
--           ∀ (I : Type) [Fintype I] (p : I → metricFrameSet g K)
--             (w : NormalWaveSpace → ℝ), ContDiff ℝ ∞ w → ∀ i₀ : I,
--           ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
--           let y := normalCoordinateMap g (p i₀) x
--           ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (normalWaveEquiv y)) →
--           let W := Real.exp (n*φ (normalWaveEquiv y))+R
--           ∀ r : ℝ, 0 ≤ r →
--           (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
--             {γ | ‖realWaveJet n W (finiteWaveSuperposition (w ∘ normalWaveEquiv)
--               (fun i ℓ => U (p i) ℓ ∘ normalWaveEquiv) γ) y‖ ≤ r} ≤
--             ENNReal.ofReal (C*n^28*r^4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.RealForm` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.PhaseSpace`, `OAI.YauCounterexamples.complexLaplaceBeltrami` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.finiteWaveSuperposition` and `OAI.YauCounterexamples.realWaveJet` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.actualHessianForm` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.metricFrameSet`, `OAI.YauCounterexamples.normalCoordinateMap`, `OAI.YauCounterexamples.normalImagCovector` and `OAI.YauCounterexamples.normalWaveProfile` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.phaseRealVector` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_compact_actual_metric_packets_supported` and `OAI.YauCounterexamples.compact_actual_waves_sign_and_jets_supported` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/PhysicalFiniteSuperpositionCompleteSupported.lean (declaration OAI.YauCounterexamples.physical_finite_superposition_complete_supported)

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

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
theorem physical_finite_superposition_complete_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O)
    (hnc : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 ≠ 0 → ∃ v,
      inner ℝ (gradient (normalWaveProfile g φ q) 0) v = 0 ∧
      ‖v‖^2 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 ∧
      0 < actualHessianForm (normalWaveProfile g φ q) (gradient (normalWaveProfile g φ q) 0)
        (gradient (normalWaveProfile g φ q) 0)+actualHessianForm (normalWaveProfile g φ q) v v)
    (hcrit : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 = 0 →
      ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (normalWaveProfile g φ q) v v)
    (m D : ℕ) :
    ∃ ρ > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Metric.ball 0 ρ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
    ∃ T > 0, ∃ c > 0, ∃ M₀ > 0, ∃ C > 0, ∃ r₀ > 0, ∃ rₑ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ n : ℝ, N ≤ n →
      ∃ (z : metricFrameSet g K → Fin 3 → Fin 3 → ℂ)
        (U : metricFrameSet g K → Fin 3 → NormalWaveSpace → ℂ),
        (∀ q ℓ, tsupport (U q ℓ) ⊆ O) ∧
        (∀ q ℓ, (∑ i, z q ℓ i*z q ℓ i = -1) ∧
          ‖phaseRealVector (z q ℓ)-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
        (∀ q ℓ, ContDiff ℝ ∞ (U q ℓ) ∧ HasCompactSupport (U q ℓ) ∧
          U q ℓ q.1.1 = Complex.exp ((n : ℂ)*(φ q.1.1 : ℂ)) ∧
          ∀ y : NormalWaveSpace, ∀ k ≤ m,
            ‖iteratedFDeriv ℝ k (U q ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-q.1.1‖^2) ∧
            ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U q ℓ) w +
              (n : ℂ)*((n : ℂ)+2)*U q ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
        (∀ q ℓ (r : ℝ), 0 ≤ r → r < rₑ → (Real.sqrt n)⁻¹ ≤ r →
          ∀ x y : NormalWaveSpace, ‖x-q.1.1‖ ≤ r → ‖y-q.1.1‖ ≤ r → n*‖y-x‖ ≤ 1 →
          ‖U q ℓ y-(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector q (z q ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U q ℓ x‖ ≤
          (M₀*r)*‖(Real.exp (n*fderiv ℝ φ x (y-x)) : ℂ)*
              Complex.exp (((n*normalImagCovector q (z q ℓ) (y-x) : ℝ) : ℂ)*Complex.I)*U q ℓ x‖) ∧
        ∀ (I : Type) [Fintype I] (p : I → metricFrameSet g K)
          (w : NormalWaveSpace → ℝ), ContDiff ℝ ∞ w → ∀ i₀ : I,
        ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
        let y := normalCoordinateMap g (p i₀) x
        ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*φ (normalWaveEquiv y)) →
        let W := Real.exp (n*φ (normalWaveEquiv y))+R
        ∀ r : ℝ, 0 ≤ r →
        (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {γ | ‖realWaveJet n W (finiteWaveSuperposition (w ∘ normalWaveEquiv)
            (fun i ℓ => U (p i) ℓ ∘ normalWaveEquiv) γ) y‖ ≤ r} ≤
          ENNReal.ofReal (C*n^28*r^4) := by
  sorry

end YauCounterexamples
end

end OAI
end
