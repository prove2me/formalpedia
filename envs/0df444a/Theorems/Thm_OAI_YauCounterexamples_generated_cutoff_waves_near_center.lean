-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_generated_cutoff_waves_near_center
-- name    : OAI.YauCounterexamples.generated_cutoff_waves_near_center
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:44:41.587988+00:00
-- url     : https://prove2.me/theorems/93f4baa0-b85e-431d-8dbd-2279acd22554
-- title:
--   OAI.YauCounterexamples.generated_cutoff_waves_near_center: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.generated_cutoff_waves_near_center` of [lean/OAI/Geometry/SmoothYau/Smoothness/ComplexPolarWeight.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ComplexPolarWeight.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Matrix`, `open scoped Topology Matrix.Norms.Elementwise`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem generated_cutoff_waves_near_center {X : Type*} [TopologicalSpace X] [CompactSpace X]
--       (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
--       (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
--       (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
--       (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
--       (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
--       (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
--       (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
--       (s : X → ℂ) (hs : Continuous s) (z : X → Fin 3 → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
--       (Q : X → ComplexPhaseMatrix) (hQ : ∀ i j, Continuous (fun p => Q p i j))
--       (hsym : ∀ p i j, Q p i j = Q p j i)
--       (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
--       (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
--       let K := 2*D+3*m+6
--       let J := D+m+1
--       let S := fun p => realPolyEval (smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1))
--       ∃ r > 0, ∃ C > 0, ∀ p (n : ℝ), 1 ≤ n → ∀ x : Fin 3 → ℝ,
--         ‖x‖ < r → ‖x‖ ≤ 1/n →
--         ‖(Complex.exp ((n : ℂ)*S p x))⁻¹*canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n x-1‖ ≤ C/n ∧
--         ‖fun i => (n : ℂ)⁻¹*(Complex.exp ((n : ℂ)*S p x))⁻¹*
--           waveDeriv (Pi.single i 1) (canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n) x-z p i‖ ≤ C/n
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ComplexPhaseMatrix` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.realPolyEval`, `OAI.YauCounterexamples.smoothPhasePolynomial` and `OAI.YauCounterexamples.waveDeriv` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.canonicalCutoffWave` (definitions bundle `OAIQ070A007` of this split).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.canonical_phase_triple_smallBall` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/ComplexPolarWeight.lean (declaration OAI.YauCounterexamples.generated_cutoff_waves_near_center)

import Mathlib
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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
open Set Filter MvPolynomial
open scoped Topology ContDiff

theorem generated_cutoff_waves_near_center {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (s : X → ℂ) (hs : Continuous s) (z : X → Fin 3 → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (Q : X → ComplexPhaseMatrix) (hQ : ∀ i j, Continuous (fun p => Q p i j))
    (hsym : ∀ p i j, Q p i j = Q p j i)
    (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
    let K := 2*D+3*m+6
    let J := D+m+1
    let S := fun p => realPolyEval (smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1))
    ∃ r > 0, ∃ C > 0, ∀ p (n : ℝ), 1 ≤ n → ∀ x : Fin 3 → ℝ,
      ‖x‖ < r → ‖x‖ ≤ 1/n →
      ‖(Complex.exp ((n : ℂ)*S p x))⁻¹*canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n x-1‖ ≤ C/n ∧
      ‖fun i => (n : ℂ)⁻¹*(Complex.exp ((n : ℂ)*S p x))⁻¹*
        waveDeriv (Pi.single i 1) (canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n) x-z p i‖ ≤ C/n := by
  sorry

end

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
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ENNReal Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end
