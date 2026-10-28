-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_normal_family_canonical_smallBall_uniform
-- name    : OAI.YauCounterexamples.normal_family_canonical_smallBall_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:09:09.311876+00:00
-- url     : https://prove2.me/theorems/a56b52a5-9ae0-4589-b939-5755816bc185
-- title:
--   OAI.YauCounterexamples.normal_family_canonical_smallBall_uniform: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.normal_family_canonical_smallBall_uniform` of [lean/OAI/Geometry/SmoothYau/Estimates/NormalFamilyCanonicalSmallBall.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/NormalFamilyCanonicalSmallBall.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Matrix`, `open scoped Topology Matrix.Norms.Elementwise`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped ContDiff Topology`, `open Set Filter MeasureTheory ProbabilityTheory Matrix`, `open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem normal_family_canonical_smallBall_uniform
--       (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
--       {K : Set NormalWaveSpace} (hK : IsCompact K)
--       (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
--       (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
--       (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
--       (hA0 : ∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0)
--       (hAd : ∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
--       (hnc : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 ≠ 0 → ∃ v,
--         inner ℝ (gradient (normalWaveProfile g φ q) 0) v = 0 ∧
--         ‖v‖^2 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 ∧
--         0 < actualHessianForm (normalWaveProfile g φ q) (gradient (normalWaveProfile g φ q) 0)
--           (gradient (normalWaveProfile g φ q) 0)+actualHessianForm (normalWaveProfile g φ q) v v)
--       (hcrit : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 = 0 →
--         ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
--           ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (normalWaveProfile g φ q) v v) :
--       ∃ κ > 0, ∃ C > 0, ∃ B > 0,
--       ∀ (ζ : (Fin 3 → ℝ) → ℂ) (_hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ),
--       ∃ r₀ > 0, ∃ C₀ > 0, ∃ N : ℝ, 1 ≤ N ∧
--         ∀ q ∈ metricFrameSet g K, ∀ (n : ℝ), N ≤ n → ∃ (z : Fin 3 → Fin 3 → ℂ) (Q : Fin 3 → ComplexPhaseMatrix),
--           (∀ ℓ, ‖z ℓ‖ ≤ B) ∧ (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) ∧
--           (∀ ℓ, PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) (z ℓ) κ C (Q ℓ)) ∧
--           (∀ ℓ, ‖phaseRealVector (z ℓ)-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
--         let U := fun ℓ => normalFamilyWave g φ A b q (z ℓ) (Q ℓ) ζ m D n
--         ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
--         ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x)) →
--         let W := Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x))+R
--         ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
--           (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
--         (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
--           {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
--             Metric.closedBall 0 r} ≤ ENNReal.ofReal (C₀*n^28*r^4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.RealForm` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.ComplexPhaseMatrix`, `OAI.YauCounterexamples.NormalWaveParameter`, `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.PhaseSpace` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.complexRealResponse` and `OAI.YauCounterexamples.complexWaveJet` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.PhaseMatrixValid` and `OAI.YauCounterexamples.actualHessianForm` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.metricFrameSet`, `OAI.YauCounterexamples.normalFamilyWave` and `OAI.YauCounterexamples.normalWaveProfile` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.phaseRealVector` (definitions bundle `OAIQ070A010` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.physical_finite_superposition_complete_supported` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/NormalFamilyCanonicalSmallBall.lean (declaration OAI.YauCounterexamples.normal_family_canonical_smallBall_uniform)

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
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
namespace YauCounterexamples

theorem normal_family_canonical_smallBall_uniform
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
    (hA0 : ∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0)
    (hAd : ∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
    (hnc : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 ≠ 0 → ∃ v,
      inner ℝ (gradient (normalWaveProfile g φ q) 0) v = 0 ∧
      ‖v‖^2 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 ∧
      0 < actualHessianForm (normalWaveProfile g φ q) (gradient (normalWaveProfile g φ q) 0)
        (gradient (normalWaveProfile g φ q) 0)+actualHessianForm (normalWaveProfile g φ q) v v)
    (hcrit : ∀ q ∈ metricFrameSet g K, gradient (normalWaveProfile g φ q) 0 = 0 →
      ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualHessianForm (normalWaveProfile g φ q) v v) :
    ∃ κ > 0, ∃ C > 0, ∃ B > 0,
    ∀ (ζ : (Fin 3 → ℝ) → ℂ) (_hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ),
    ∃ r₀ > 0, ∃ C₀ > 0, ∃ N : ℝ, 1 ≤ N ∧
      ∀ q ∈ metricFrameSet g K, ∀ (n : ℝ), N ≤ n → ∃ (z : Fin 3 → Fin 3 → ℂ) (Q : Fin 3 → ComplexPhaseMatrix),
        (∀ ℓ, ‖z ℓ‖ ≤ B) ∧ (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) ∧
        (∀ ℓ, PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) (z ℓ) κ C (Q ℓ)) ∧
        (∀ ℓ, ‖phaseRealVector (z ℓ)-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹) ∧
      let U := fun ℓ => normalFamilyWave g φ A b q (z ℓ) (Q ℓ) ζ m D n
      ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
      ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x)) →
      let W := Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x))+R
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
          Metric.closedBall 0 r} ≤ ENNReal.ofReal (C₀*n^28*r^4) := by
  sorry

end YauCounterexamples

end

end OAI
end
