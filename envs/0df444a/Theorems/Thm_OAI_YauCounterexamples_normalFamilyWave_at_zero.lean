-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_normalFamilyWave_at_zero
-- name    : OAI.YauCounterexamples.normalFamilyWave_at_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:46:16.540866+00:00
-- url     : https://prove2.me/theorems/a3c32012-7b94-4fa7-8ad9-cabe834f9765
-- title:
--   OAI.YauCounterexamples.normalFamilyWave_at_zero: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.normalFamilyWave_at_zero` of [lean/OAI/Geometry/SmoothYau/Estimates/NormalFamilyWaveZero.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/NormalFamilyWaveZero.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Matrix`, `open scoped Topology Matrix.Norms.Elementwise`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter Matrix`, `open scoped Topology ContDiff Matrix.Norms.Elementwise`):
--
--   ```lean
--   lemma normalFamilyWave_at_zero (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       (φ : NormalWaveSpace → ℝ)
--       (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
--       (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
--       (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b) (q : NormalWaveParameter)
--       (hA0 : ∀ i j, A (q,0) i j = if i = j then 1 else 0)
--       (hAd : ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
--       (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix) {κ C : ℝ}
--       (hQ : PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q)
--       (hnQ : ∑ i, z i*z i = -1) (ζ : (Fin 3 → ℝ) → ℂ)
--       (hζ0 : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) (n : ℝ) :
--       normalFamilyWave g φ A b q z Q ζ m D n 0 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ComplexPhaseMatrix`, `OAI.YauCounterexamples.NormalWaveParameter` and `OAI.YauCounterexamples.NormalWaveSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.PhaseMatrixValid` and `OAI.YauCounterexamples.actualHessianForm` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.normalFamilyWave` and `OAI.YauCounterexamples.normalWaveProfile` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.uniform_localized_physical_waves_with_coordinates_supported` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/NormalFamilyWaveZero.lean (declaration OAI.YauCounterexamples.normalFamilyWave_at_zero)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma normalFamilyWave_at_zero (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b) (q : NormalWaveParameter)
    (hA0 : ∀ i j, A (q,0) i j = if i = j then 1 else 0)
    (hAd : ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
    (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix) {κ C : ℝ}
    (hQ : PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q)
    (hnQ : ∑ i, z i*z i = -1) (ζ : (Fin 3 → ℝ) → ℂ)
    (hζ0 : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) (n : ℝ) :
    normalFamilyWave g φ A b q z Q ζ m D n 0 = Complex.exp ((n : ℂ)*(φ q.1 : ℂ)) := by
  sorry

end YauCounterexamples

end

end OAI
end
