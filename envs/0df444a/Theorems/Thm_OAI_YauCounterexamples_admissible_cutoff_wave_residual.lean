-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_admissible_cutoff_wave_residual
-- name    : OAI.YauCounterexamples.admissible_cutoff_wave_residual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:55:04.873656+00:00
-- url     : https://prove2.me/theorems/fb2f2e2d-c16c-4a7e-b43c-5c2e58368b2d
-- title:
--   OAI.YauCounterexamples.admissible_cutoff_wave_residual: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.admissible_cutoff_wave_residual` of [lean/OAI/Geometry/SmoothYau/Estimates/CanonicalCutoffWave.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/CanonicalCutoffWave.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open scoped Topology`, `open Set Filter Matrix MvPolynomial`, `open scoped Topology ContDiff Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem admissible_cutoff_wave_residual {X : Type*} [TopologicalSpace X] [CompactSpace X]
--       (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
--       (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
--       (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
--       (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
--       (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
--       (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
--       (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
--       (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
--       (hφ0 : Continuous (fun p => φ p 0))
--       (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
--       (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
--       ∃ r > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
--         ∃ A > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
--           PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
--           ∀ n : ℝ, 1 ≤ n → ‖phaseRealVector z-gradient (φ p) 0‖ ≤ (Real.sqrt n)⁻¹ →
--           ∀ x ∈ Metric.ball (0 : Fin 3 → ℝ) r, ∀ k ≤ m,
--             ‖iteratedFDeriv ℝ k (fun y =>
--               waveCoordinateOperator (fun i => Pi.single i 1) (g p) (b p)
--                 (canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n) y +
--               (n : ℂ)*((n : ℂ)+2)*canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n y) x‖ ≤
--               A*(n^(D+1))⁻¹*Real.exp (n*φ p (WithLp.toLp 2 x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ComplexPhaseMatrix` and `OAI.YauCounterexamples.PhaseSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.PhaseMatrixValid` and `OAI.YauCounterexamples.actualHessianForm` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.canonicalCutoffWave` and `OAI.YauCounterexamples.waveCoordinateOperator` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.phaseRealVector` (definitions bundle `OAIQ070A010` of this split).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.normal_family_wave_localized_estimates` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/CanonicalCutoffWave.lean (declaration OAI.YauCounterexamples.admissible_cutoff_wave_residual)

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
namespace YauCounterexamples

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
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem admissible_cutoff_wave_residual {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
    ∃ r > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ A > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
        ∀ n : ℝ, 1 ≤ n → ‖phaseRealVector z-gradient (φ p) 0‖ ≤ (Real.sqrt n)⁻¹ →
        ∀ x ∈ Metric.ball (0 : Fin 3 → ℝ) r, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k (fun y =>
            waveCoordinateOperator (fun i => Pi.single i 1) (g p) (b p)
              (canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n) y +
            (n : ℂ)*((n : ℂ)+2)*canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n y) x‖ ≤
            A*(n^(D+1))⁻¹*Real.exp (n*φ p (WithLp.toLp 2 x)) := by
  sorry

end YauCounterexamples
end

end OAI
end
