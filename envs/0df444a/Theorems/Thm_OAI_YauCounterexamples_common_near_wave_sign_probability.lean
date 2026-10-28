-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_common_near_wave_sign_probability
-- name    : OAI.YauCounterexamples.common_near_wave_sign_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:22:28.567095+00:00
-- url     : https://prove2.me/theorems/ba209ad7-4828-4318-80b1-8cf2e99ccf93
-- title:
--   OAI.YauCounterexamples.common_near_wave_sign_probability: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.common_near_wave_sign_probability` of [lean/OAI/Geometry/SmoothYau/SphereMetric/UnitCorrelationSymm.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/UnitCorrelationSymm.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set MeasureTheory ProbabilityTheory`, `open scoped RealInnerProductSpace ENNReal`):
--
--   ```lean
--   theorem common_near_wave_sign_probability {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
--       ∃ q > 0, ∀ (I : Type) [Fintype I] (z v : I → ℂ) (w : Fin 3 → I → ℂ)
--         (α : Fin 3 → ℝ) (θ : I → Fin 3 → ℝ) (m : ℝ) (m' : Fin 3 → ℝ) (δ : ℝ),
--         complexValueVector z ≠ 0 → (∀ j, 0 < α j) → δ ≤ 1/16 → δ ≤ κ/96 →
--         (∀ i j, |θ i j| ≤ 1) → (∀ i, κ ≤ ∑ j, (θ i j)^2) →
--         ‖complexValueVector z-complexValueVector v‖ ≤ δ*‖complexValueVector z‖ →
--         (∀ j, ‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)
--           -complexValueVector (w j)‖ ≤
--           δ*‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)‖) →
--         |m/‖complexValueVector v‖| ≤ 1 → (∀ j, |m' j/‖complexValueVector (w j)‖| ≤ 1) →
--         ∃ j, ENNReal.ofReal q ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
--           {γ | (m+complexGaussianRealValue v γ)*(m' j+complexGaussianRealValue (w j) γ) < 0}
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.complexGaussianRealValue` and `OAI.YauCounterexamples.complexValueVector` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.rotatedWaveValues` (definitions bundle `OAIQ070A004` of this split).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.finite_near_far_sign_probability` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/UnitCorrelationSymm.lean (declaration OAI.YauCounterexamples.common_near_wave_sign_probability)

import Mathlib
import Definitions.Def_OAIQ070A003
import Definitions.Def_OAIQ070A004

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
namespace YauCounterexamples

theorem common_near_wave_sign_probability {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ q > 0, ∀ (I : Type) [Fintype I] (z v : I → ℂ) (w : Fin 3 → I → ℂ)
      (α : Fin 3 → ℝ) (θ : I → Fin 3 → ℝ) (m : ℝ) (m' : Fin 3 → ℝ) (δ : ℝ),
      complexValueVector z ≠ 0 → (∀ j, 0 < α j) → δ ≤ 1/16 → δ ≤ κ/96 →
      (∀ i j, |θ i j| ≤ 1) → (∀ i, κ ≤ ∑ j, (θ i j)^2) →
      ‖complexValueVector z-complexValueVector v‖ ≤ δ*‖complexValueVector z‖ →
      (∀ j, ‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)
        -complexValueVector (w j)‖ ≤
        δ*‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ i j) i)‖) →
      |m/‖complexValueVector v‖| ≤ 1 → (∀ j, |m' j/‖complexValueVector (w j)‖| ≤ 1) →
      ∃ j, ENNReal.ofReal q ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (m+complexGaussianRealValue v γ)*(m' j+complexGaussianRealValue (w j) γ) < 0} := by
  sorry

end YauCounterexamples
end

end OAI
end
