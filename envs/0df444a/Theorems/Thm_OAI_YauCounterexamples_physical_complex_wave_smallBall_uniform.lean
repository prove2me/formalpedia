-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_physical_complex_wave_smallBall_uniform
-- name    : OAI.YauCounterexamples.physical_complex_wave_smallBall_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:09:04.426217+00:00
-- url     : https://prove2.me/theorems/3a03b05e-065a-4b8e-9ffc-18b58b09a0cf
-- title:
--   OAI.YauCounterexamples.physical_complex_wave_smallBall_uniform: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.physical_complex_wave_smallBall_uniform` of [lean/OAI/Geometry/SmoothYau/Smoothness/SelectedComplexJetMatrixScale.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/SelectedComplexJetMatrixScale.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Matrix`, `open scoped Topology Matrix.Norms.Elementwise`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set MeasureTheory ProbabilityTheory Matrix`, `open scoped ENNReal Topology Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem physical_complex_wave_smallBall_uniform (M C η : ℝ) (hM : 1 ≤ M)
--       (hC : 0 ≤ C) (hη : 0 < η) :
--       ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
--         ∀ a ν b c : PhaseSpace, ‖a‖ ≤ M → ‖ν‖ = 1 →
--           inner ℝ ν b = 0 → inner ℝ ν c = 0 →
--           ‖b‖^2 = 1+‖a‖^2 → ‖c‖^2 = 1+‖a‖^2 →
--           ‖b‖ ≤ M → ‖c‖ ≤ M → η ≤ transverseAngleSq b c →
--         ∀ J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ,
--           ‖selectedComplexJetMatrix J-physicalWaveJetMatrix a ν b c δ‖ ≤ C*δ^2 →
--         ∀ q : ℝ, 0 < q → ∀ w : Fin 3 → ℝ, (∀ i, q ≤ w i) → ∀ e : Fin 3 → Circle,
--         ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
--           (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
--         (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
--           {v | complexRealResponse (fun ℓ i => (e ℓ : ℂ)*((w ℓ : ℂ)*J ℓ i)) v.2+noise v.1 ∈
--             Metric.closedBall 0 r} ≤
--         ENNReal.ofReal (Real.sqrt η/2*δ*q^4)⁻¹*(ENNReal.ofReal (2*r))^4
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.PhaseSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.complexRealResponse` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.selectedComplexJetMatrix` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.transverseAngleSq` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.physicalWaveJetMatrix` (definitions bundle `OAIQ070A010` of this split).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.canonical_phase_triple_smallBall` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/SelectedComplexJetMatrixScale.lean (declaration OAI.YauCounterexamples.physical_complex_wave_smallBall_uniform)

import Mathlib
import Definitions.Def_OAIQ070A010

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal Topology Matrix.Norms.Elementwise
namespace YauCounterexamples

theorem physical_complex_wave_smallBall_uniform (M C η : ℝ) (hM : 1 ≤ M)
    (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      ∀ a ν b c : PhaseSpace, ‖a‖ ≤ M → ‖ν‖ = 1 →
        inner ℝ ν b = 0 → inner ℝ ν c = 0 →
        ‖b‖^2 = 1+‖a‖^2 → ‖c‖^2 = 1+‖a‖^2 →
        ‖b‖ ≤ M → ‖c‖ ≤ M → η ≤ transverseAngleSq b c →
      ∀ J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ,
        ‖selectedComplexJetMatrix J-physicalWaveJetMatrix a ν b c δ‖ ≤ C*δ^2 →
      ∀ q : ℝ, 0 < q → ∀ w : Fin 3 → ℝ, (∀ i, q ≤ w i) → ∀ e : Fin 3 → Circle,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ i => (e ℓ : ℂ)*((w ℓ : ℂ)*J ℓ i)) v.2+noise v.1 ∈
          Metric.closedBall 0 r} ≤
      ENNReal.ofReal (Real.sqrt η/2*δ*q^4)⁻¹*(ENNReal.ofReal (2*r))^4 := by
  sorry

end YauCounterexamples
end

end OAI
end
