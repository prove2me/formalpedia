-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_all_admissible_generated_gaussian
-- name    : OAI.YauCounterexamples.all_admissible_generated_gaussian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:59:31.731409+00:00
-- url     : https://prove2.me/theorems/c21490f2-3d9f-4589-a091-103d6a282934
-- title:
--   OAI.YauCounterexamples.all_admissible_generated_gaussian: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.all_admissible_generated_gaussian` of [lean/OAI/Geometry/SmoothYau/Geometry/ActualHessianForm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ActualHessianForm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Matrix MvPolynomial`, `open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem all_admissible_generated_gaussian {X : Type*} [TopologicalSpace X] [CompactSpace X]
--       (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
--       (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
--       (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
--       (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
--       (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
--       (hφ0 : Continuous (fun p => φ p 0))
--       (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
--       (L : ℕ) (hL : 2 ≤ L)
--       (hgj : ∀ i j k, k < L → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0))
--       (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) :
--       ∃ r > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
--         PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
--         ∀ x ∈ Metric.ball (0 : PhaseSpace) r,
--         (realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z Q L) (fun i => x i)).re -
--           φ p x ≤ ‖phaseRealVector z-gradient (φ p) 0‖*‖x‖-κ*‖x‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ComplexPhaseMatrix` and `OAI.YauCounterexamples.PhaseSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.realPolyEval` and `OAI.YauCounterexamples.smoothPhasePolynomial` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.PhaseMatrixValid` and `OAI.YauCounterexamples.actualHessianForm` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.phaseRealVector` (definitions bundle `OAIQ070A010` of this split).
--
--   **Used by.** The proofs of `OAI.YauCounterexamples.admissible_cutoff_wave_residual` and `OAI.YauCounterexamples.normal_family_wave_localized_estimates` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/ActualHessianForm.lean (declaration OAI.YauCounterexamples.all_admissible_generated_gaussian)

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
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples

theorem all_admissible_generated_gaussian {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (L : ℕ) (hL : 2 ≤ L)
    (hgj : ∀ i j k, k < L → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0))
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ r > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
      PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
      ∀ x ∈ Metric.ball (0 : PhaseSpace) r,
      (realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z Q L) (fun i => x i)).re -
        φ p x ≤ ‖phaseRealVector z-gradient (φ p) 0‖*‖x‖-κ*‖x‖^2 := by
  sorry

end YauCounterexamples

end

end OAI
end
