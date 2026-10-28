-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_finite_near_far_sign_probability
-- name    : OAI.YauCounterexamples.finite_near_far_sign_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:23:55.605592+00:00
-- url     : https://prove2.me/theorems/2afa7c80-5c05-499e-b0d9-466dc3be611d
-- title:
--   OAI.YauCounterexamples.finite_near_far_sign_probability: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.finite_near_far_sign_probability` of [lean/OAI/Geometry/SmoothYau/Estimates/LocalizedPacketSignProbability.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/LocalizedPacketSignProbability.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology ENNReal RealInnerProductSpace`):
--
--   ```lean
--   theorem finite_near_far_sign_probability {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
--       ∃ p > 0, ∀ (I : Type) [Fintype I] [DecidableEq I]
--         (s : Finset I) (v : I → ℂ) (w : Fin 3 → I → ℂ) (α : Fin 3 → ℝ)
--         (θ : I → Fin 3 → ℝ) (m : ℝ) (m' : Fin 3 → ℝ) (A ε δ τ₀ : ℝ) (τ : Fin 3 → ℝ),
--         0 < A → 0 ≤ ε → ε ≤ δ → 0 ≤ τ₀ → (∀ j, 0 ≤ τ j) →
--         (∃ i ∈ s, A ≤ ‖v i‖) → (∀ j, 0 < α j) → δ ≤ 1/16 → δ ≤ κ/96 →
--         (∀ i ∈ s, ∀ j, |θ i j| ≤ 1) → (∀ i ∈ s, κ ≤ ∑ j, (θ i j)^2) →
--         (∀ i ∉ s, ‖v i‖ ≤ τ₀) → (Fintype.card I : ℝ)*τ₀ ≤ δ*A →
--         (∀ j, (Fintype.card I : ℝ)*τ j ≤ (δ-ε)*α j*A) →
--         (∀ j i, i ∈ s →
--           ‖(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*v i-w j i‖ ≤
--             ε*‖(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*v i‖) →
--         (∀ j i, i ∉ s → ‖w j i‖ ≤ τ j) →
--         |m/‖complexValueVector v‖| ≤ 1 → (∀ j, |m' j/‖complexValueVector (w j)‖| ≤ 1) →
--         ∃ j, ENNReal.ofReal p ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
--           {γ | (m+complexGaussianRealValue v γ)*(m' j+complexGaussianRealValue (w j) γ) < 0}
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.complexGaussianRealValue` and `OAI.YauCounterexamples.complexValueVector` (definitions bundle `OAIQ070A003` of this split).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.localized_packet_sign_probability` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/LocalizedPacketSignProbability.lean (declaration OAI.YauCounterexamples.finite_near_far_sign_probability)

import Mathlib
import Definitions.Def_OAIQ070A003

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
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

theorem finite_near_far_sign_probability {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ p > 0, ∀ (I : Type) [Fintype I] [DecidableEq I]
      (s : Finset I) (v : I → ℂ) (w : Fin 3 → I → ℂ) (α : Fin 3 → ℝ)
      (θ : I → Fin 3 → ℝ) (m : ℝ) (m' : Fin 3 → ℝ) (A ε δ τ₀ : ℝ) (τ : Fin 3 → ℝ),
      0 < A → 0 ≤ ε → ε ≤ δ → 0 ≤ τ₀ → (∀ j, 0 ≤ τ j) →
      (∃ i ∈ s, A ≤ ‖v i‖) → (∀ j, 0 < α j) → δ ≤ 1/16 → δ ≤ κ/96 →
      (∀ i ∈ s, ∀ j, |θ i j| ≤ 1) → (∀ i ∈ s, κ ≤ ∑ j, (θ i j)^2) →
      (∀ i ∉ s, ‖v i‖ ≤ τ₀) → (Fintype.card I : ℝ)*τ₀ ≤ δ*A →
      (∀ j, (Fintype.card I : ℝ)*τ j ≤ (δ-ε)*α j*A) →
      (∀ j i, i ∈ s →
        ‖(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*v i-w j i‖ ≤
          ε*‖(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*v i‖) →
      (∀ j i, i ∉ s → ‖w j i‖ ≤ τ j) →
      |m/‖complexValueVector v‖| ≤ 1 → (∀ j, |m' j/‖complexValueVector (w j)‖| ≤ 1) →
      ∃ j, ENNReal.ofReal p ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (m+complexGaussianRealValue v γ)*(m' j+complexGaussianRealValue (w j) γ) < 0} := by
  sorry
end

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

end YauCounterexamples
end

end OAI
end
