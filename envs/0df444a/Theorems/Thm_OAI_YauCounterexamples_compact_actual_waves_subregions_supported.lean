-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_compact_actual_waves_subregions_supported
-- name    : OAI.YauCounterexamples.compact_actual_waves_subregions_supported
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:58:52.483002+00:00
-- url     : https://prove2.me/theorems/c165fe5f-7347-4776-910a-f52eb4a622b6
-- title:
--   OAI.YauCounterexamples.compact_actual_waves_subregions_supported: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.compact_actual_waves_subregions_supported` of [lean/OAI/Geometry/SmoothYau/Limits/CompactActualWavesSubregionsSupported.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CompactActualWavesSubregionsSupported.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter Metric`, `open scoped Topology InnerProductSpace`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Function Metric`, `open scoped Topology`, `open Set Filter Manifold`, `open scoped Topology ContDiff`, `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   theorem compact_actual_waves_subregions_supported
--       (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       {K : Set NormalWaveSpace} (hK : IsCompact K)
--       {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
--       ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
--       ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
--       (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
--       (∀ x ∈ K, fderiv ℝ φ x = 0 →
--         ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
--           ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
--       ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ T > 0, ∃ c > 0, ∃ Q > 0,
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
--         ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
--           ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
--           ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
--           ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
--           (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
--           (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
--           (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
--           (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
--           ∀ J : Set NormalWaveSpace, J ⊆ K →
--           (∀ y ∈ J, |w y| ≤ c₀*Real.exp (n*φ y)) →
--           ∀ (P : Type) [Fintype P] (ℓ q : P → ℝ), (∀ a, 0 ≤ q a) →
--           ∀ ν : P → Measure NormalWaveSpace, ∀ _ : ∀ a, IsFiniteMeasure (ν a),
--           0 < ∑ a, q a*(ν a univ).toReal →
--           (∀ a, ∀ᵐ x ∂ν a, x ∈ J ∧ profileFrequencyScale g φ x ≤ ℓ a ∧
--             ℓ a ≤ 2*profileFrequencyScale g φ x ∧ (∀ j, packetAxisShift x n ε (ℓ a) j ∈ J)) →
--           ∃ γ : t → Fin 3 → ℂ, (∀ i j, ‖γ i j‖ ≤ n) ∧
--             (∀ y ∈ E, 1/n^110 ≤
--               ‖realWaveJet n (W y) (finiteWaveSuperposition (w ∘ normalWaveEquiv)
--                 (fun i j => U i j ∘ normalWaveEquiv) γ) y‖) ∧
--             (p₀/2)*(∑ a, q a*(ν a univ).toReal) <
--               ∑ a, q a*∑ j : Fin 3, (ν a {x | finiteWaveSuperposition w U γ x *
--                 finiteWaveSuperposition w U γ (packetAxisShift x n ε (ℓ a) j) < 0}).toReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.CoordinateForm`, `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.actualCoordinateHessian`, `OAI.YauCounterexamples.complexLaplaceBeltrami` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.finiteWaveSuperposition` and `OAI.YauCounterexamples.realWaveJet` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.metricFrameSet` and `OAI.YauCounterexamples.packetAxisShift` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.actualProfileStrict` (definitions bundle `OAIQ070A009` of this split); `OAI.YauCounterexamples.profileFrequencyScale` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_exists_metric_sign_quasimodes_subregions_supported` and `OAI.YauCounterexamples.exists_supported_nodal_quasimodes_subregions` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Limits/CompactActualWavesSubregionsSupported.lean (declaration OAI.YauCounterexamples.compact_actual_waves_subregions_supported)

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

theorem compact_actual_waves_subregions_supported
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ T > 0, ∃ c > 0, ∃ Q > 0,
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
      ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        ∀ J : Set NormalWaveSpace, J ⊆ K →
        (∀ y ∈ J, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∀ (P : Type) [Fintype P] (ℓ q : P → ℝ), (∀ a, 0 ≤ q a) →
        ∀ ν : P → Measure NormalWaveSpace, ∀ _ : ∀ a, IsFiniteMeasure (ν a),
        0 < ∑ a, q a*(ν a univ).toReal →
        (∀ a, ∀ᵐ x ∂ν a, x ∈ J ∧ profileFrequencyScale g φ x ≤ ℓ a ∧
          ℓ a ≤ 2*profileFrequencyScale g φ x ∧ (∀ j, packetAxisShift x n ε (ℓ a) j ∈ J)) →
        ∃ γ : t → Fin 3 → ℂ, (∀ i j, ‖γ i j‖ ≤ n) ∧
          (∀ y ∈ E, 1/n^110 ≤
            ‖realWaveJet n (W y) (finiteWaveSuperposition (w ∘ normalWaveEquiv)
              (fun i j => U i j ∘ normalWaveEquiv) γ) y‖) ∧
          (p₀/2)*(∑ a, q a*(ν a univ).toReal) <
            ∑ a, q a*∑ j : Fin 3, (ν a {x | finiteWaveSuperposition w U γ x *
              finiteWaveSuperposition w U γ (packetAxisShift x n ε (ℓ a) j) < 0}).toReal := by
  sorry

end YauCounterexamples
end

end OAI
end
