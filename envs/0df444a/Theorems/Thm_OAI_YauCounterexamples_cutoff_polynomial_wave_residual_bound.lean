-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_cutoff_polynomial_wave_residual_bound
-- name    : OAI.YauCounterexamples.cutoff_polynomial_wave_residual_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:39:41.189083+00:00
-- url     : https://prove2.me/theorems/e001d884-fb0a-4ff7-b8df-c7dd4a5e8829
-- title:
--   OAI.YauCounterexamples.cutoff_polynomial_wave_residual_bound: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.cutoff_polynomial_wave_residual_bound` of [lean/OAI/Geometry/SmoothYau/Smoothness/SmoothFiniteWaveSum.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/SmoothFiniteWaveSum.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem cutoff_polynomial_wave_residual_bound
--       (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
--       (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
--       (S : X → MvPolynomial σ ℂ) (V : X → ℕ → MvPolynomial σ ℂ)
--       (ζ : (σ → ℝ) → ℂ) (hζ : ContDiff ℝ ∞ ζ) (hζ₀ : ζ =ᶠ[𝓝 0] fun _ => 1)
--       (m D J : ℕ) (hJ : D+m+1 ≤ J) (r c : ℝ) (hr : r ≤ 1) (hc : 0 < c)
--       (P : Set X)
--       (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) P (Metric.ball 0 r))
--       (hbB : ∀ i, UniformJetBounds (fun p => b p i) P (Metric.ball 0 r))
--       (hSB : UniformJetBounds (fun p => realPolyEval (S p)) P (Metric.ball 0 r))
--       (hVB : ∀ j, UniformJetBounds (fun p => realPolyEval (V p j)) P (Metric.ball 0 r))
--       (hFzero : ∀ p ∈ P, ∀ j, SmoothJetZero
--         (fun x => smoothEikonalResidual (g p) (S p) x * realPolyEval (V p j) x) (2*D+3*m+6))
--       (hRzero : ∀ p ∈ P, ∀ j ≤ J, SmoothJetZero
--         (polynomialWaveRemainder (g p) (b p) (S p) (V p) j) (2*D+3*m+6)) :
--       ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
--         ∀ φ : ℝ, n*((realPolyEval (S p) x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 →
--         ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun y =>
--           waveCoordinateOperator (fun i => Pi.single i 1) (g p) (b p)
--             (smoothFiniteWave (realPolyEval (S p)) (fun j x => ζ x * realPolyEval (V p j) x) J n) y +
--            (n : ℂ)*((n : ℂ)+2)*smoothFiniteWave (realPolyEval (S p))
--             (fun j x => ζ x * realPolyEval (V p j) x) J n y) x‖ ≤
--           C*(n^(D+1))⁻¹*Real.exp (n*φ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.SmoothJetZero` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.UniformJetBounds`, `OAI.YauCounterexamples.realPolyEval` and `OAI.YauCounterexamples.smoothFiniteWave` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.polynomialWaveRemainder`, `OAI.YauCounterexamples.smoothEikonalResidual` and `OAI.YauCounterexamples.waveCoordinateOperator` (definitions bundle `OAIQ070A007` of this split).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.admissible_cutoff_wave_residual` and `OAI_YauCounterexamples_generated_cutoff_wave_residual_estimate` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/SmoothFiniteWaveSum.lean (declaration OAI.YauCounterexamples.cutoff_polynomial_wave_residual_bound)

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
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {X : Type*}

theorem cutoff_polynomial_wave_residual_bound
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (S : X → MvPolynomial σ ℂ) (V : X → ℕ → MvPolynomial σ ℂ)
    (ζ : (σ → ℝ) → ℂ) (hζ : ContDiff ℝ ∞ ζ) (hζ₀ : ζ =ᶠ[𝓝 0] fun _ => 1)
    (m D J : ℕ) (hJ : D+m+1 ≤ J) (r c : ℝ) (hr : r ≤ 1) (hc : 0 < c)
    (P : Set X)
    (hgB : ∀ i j, UniformJetBounds (fun p => g p i j) P (Metric.ball 0 r))
    (hbB : ∀ i, UniformJetBounds (fun p => b p i) P (Metric.ball 0 r))
    (hSB : UniformJetBounds (fun p => realPolyEval (S p)) P (Metric.ball 0 r))
    (hVB : ∀ j, UniformJetBounds (fun p => realPolyEval (V p j)) P (Metric.ball 0 r))
    (hFzero : ∀ p ∈ P, ∀ j, SmoothJetZero
      (fun x => smoothEikonalResidual (g p) (S p) x * realPolyEval (V p j) x) (2*D+3*m+6))
    (hRzero : ∀ p ∈ P, ∀ j ≤ J, SmoothJetZero
      (polynomialWaveRemainder (g p) (b p) (S p) (V p) j) (2*D+3*m+6)) :
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
      ∀ φ : ℝ, n*((realPolyEval (S p) x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun y =>
        waveCoordinateOperator (fun i => Pi.single i 1) (g p) (b p)
          (smoothFiniteWave (realPolyEval (S p)) (fun j x => ζ x * realPolyEval (V p j) x) J n) y +
         (n : ℂ)*((n : ℂ)+2)*smoothFiniteWave (realPolyEval (S p))
          (fun j x => ζ x * realPolyEval (V p j) x) J n y) x‖ ≤
        C*(n^(D+1))⁻¹*Real.exp (n*φ) := by
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
open Set Filter
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end
