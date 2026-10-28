-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_compact_actual_sign_noncancellation_supported
-- name    : OAI.YauCounterexamples.compact_actual_sign_noncancellation_supported
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:01:50.074864+00:00
-- url     : https://prove2.me/theorems/e1ef42f0-2c56-498b-a8a3-a4df516e66b8
-- title:
--   OAI.YauCounterexamples.compact_actual_sign_noncancellation_supported: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.compact_actual_sign_noncancellation_supported` of [lean/OAI/Geometry/SmoothYau/Limits/CompactActualWavesSubregionsSupported.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CompactActualWavesSubregionsSupported.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   theorem compact_actual_sign_noncancellation_supported
--       (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       {K : Set NormalWaveSpace} (hK : IsCompact K)
--       {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
--       ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
--       ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
--       (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
--       (∀ x ∈ K, fderiv ℝ φ x = 0 →
--         ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
--           ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
--       ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ T > 0, ∃ c > 0, ∃ A > 0, ∃ Q > 0,
--       ∃ N : ℝ, 2 ≤ N ∧ ∀ s : ℝ, N ≤ s →
--       let n := s^4
--       ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
--       ∃ U : t → Fin 3 → NormalWaveSpace → ℂ,
--         (∀ i ℓ, tsupport (U i ℓ) ⊆ O) ∧
--         (t.card : ℝ) ≤ Q*n^3 ∧
--         (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
--           U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
--           ∀ y : NormalWaveSpace, ∀ k ≤ max m 2,
--             ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-(p i).1.1‖^2) ∧
--             ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U i ℓ) w +
--               (n : ℂ)*((n : ℂ)+2)*U i ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
--         (∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
--           ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
--           ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
--           ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
--           (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
--           (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
--           (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
--           (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
--           (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
--             {γ | (∃ i ℓ, n < ‖γ i ℓ‖) ∨ ∃ y ∈ E,
--               ‖realWaveJet n (W y) (finiteWaveSuperposition (w ∘ normalWaveEquiv)
--                 (fun i ℓ => U i ℓ ∘ normalWaveEquiv) γ) y‖ < 1/n^110} ≤
--             ENNReal.ofReal (A/n^5)) ∧
--         ∀ b : NormalWaveSpace → ℝ, (∀ y ∈ K, |b y| ≤ c₀*Real.exp (n*φ y)) →
--         ∀ x ∈ K, ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
--         (∀ j, packetAxisShift x n ε ℓ j ∈ K) →
--         ∃ j, ENNReal.ofReal p₀ ≤ (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
--           {γ | finiteWaveSuperposition b U γ x *
--             finiteWaveSuperposition b U γ (packetAxisShift x n ε ℓ j) < 0}
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CoordinateForm`, `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.actualCoordinateHessian`, `OAI.YauCounterexamples.complexLaplaceBeltrami` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.finiteWaveSuperposition` and `OAI.YauCounterexamples.realWaveJet` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.metricFrameSet` and `OAI.YauCounterexamples.packetAxisShift` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.actualProfileStrict` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.profileFrequencyScale` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.compact_actual_waves_subregions_supported` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CompactActualWavesSubregionsSupported.lean (declaration OAI.YauCounterexamples.compact_actual_sign_noncancellation_supported)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
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
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem compact_actual_sign_noncancellation_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ T > 0, ∃ c > 0, ∃ A > 0, ∃ Q > 0,
    ∃ N : ℝ, 2 ≤ N ∧ ∀ s : ℝ, N ≤ s →
    let n := s^4
    ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
    ∃ U : t → Fin 3 → NormalWaveSpace → ℂ,
      (∀ i ℓ, tsupport (U i ℓ) ⊆ O) ∧
      (t.card : ℝ) ≤ Q*n^3 ∧
      (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
        U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
        ∀ y : NormalWaveSpace, ∀ k ≤ max m 2,
          ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-(p i).1.1‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U i ℓ) w +
            (n : ℂ)*((n : ℂ)+2)*U i ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
      (∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {γ | (∃ i ℓ, n < ‖γ i ℓ‖) ∨ ∃ y ∈ E,
            ‖realWaveJet n (W y) (finiteWaveSuperposition (w ∘ normalWaveEquiv)
              (fun i ℓ => U i ℓ ∘ normalWaveEquiv) γ) y‖ < 1/n^110} ≤
          ENNReal.ofReal (A/n^5)) ∧
      ∀ b : NormalWaveSpace → ℝ, (∀ y ∈ K, |b y| ≤ c₀*Real.exp (n*φ y)) →
      ∀ x ∈ K, ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
      (∀ j, packetAxisShift x n ε ℓ j ∈ K) →
      ∃ j, ENNReal.ofReal p₀ ≤ (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {γ | finiteWaveSuperposition b U γ x *
          finiteWaveSuperposition b U γ (packetAxisShift x n ε ℓ j) < 0} := by
  sorry

end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

end YauCounterexamples
end

end OAI
end
