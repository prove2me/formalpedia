-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_threePacket_background_input_bounds
-- name    : OAI.YauCounterexamples.threePacket_background_input_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T12:12:29.736561+00:00
-- url     : https://prove2.me/theorems/90c58704-7b4a-4f7d-899c-377213db1378
-- title:
--   OAI.YauCounterexamples.threePacket_background_input_bounds: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.threePacket_background_input_bounds` of [lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeExceptional.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeExceptional.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter Function Manifold Metric`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma threePacket_background_input_bounds {φ : ThreeManifold → ℝ}
--       (hφ : ContDiff ℝ ∞ (φ ∘ threeNormalInv)) {S : Set (Fin 3 → ℝ)} (hS : IsCompact S) :
--       ∃ T>0, ∃ H>0, ∀ k : ℕ, 2≤k →
--         Differentiable ℝ (threePacketWeight φ k) ∧ (∀ y, 0<threePacketWeight φ k y) ∧
--         (∀ y∈S, ∀ j≤2,
--           ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius k ∘ threeNormalInv) ∘ normalWaveEquiv) y‖ ≤
--             T*(productWaveFrequency k)^j*threePacketWeight φ k y) ∧
--         (∀ y∈S, ‖fderiv ℝ (threePacketWeight φ k) y‖ ≤ H*productWaveFrequency k*threePacketWeight φ k y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreeManifold` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.productWaveFrequency` and `OAI.YauCounterexamples.threeCouplingRadius` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.threeNormalInv` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.threeCoupled` and `OAI.YauCounterexamples.threePacketWeight` (definitions bundle `OAIQ070A010` of this split).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.exists_three_chart_quasimodes_with_gaps` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/ThreeExceptional.lean (declaration OAI.YauCounterexamples.threePacket_background_input_bounds)

import Mathlib
import Definitions.Def_OAIQ070A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma threePacket_background_input_bounds {φ : ThreeManifold → ℝ}
    (hφ : ContDiff ℝ ∞ (φ ∘ threeNormalInv)) {S : Set (Fin 3 → ℝ)} (hS : IsCompact S) :
    ∃ T>0, ∃ H>0, ∀ k : ℕ, 2≤k →
      Differentiable ℝ (threePacketWeight φ k) ∧ (∀ y, 0<threePacketWeight φ k y) ∧
      (∀ y∈S, ∀ j≤2,
        ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius k ∘ threeNormalInv) ∘ normalWaveEquiv) y‖ ≤
          T*(productWaveFrequency k)^j*threePacketWeight φ k y) ∧
      (∀ y∈S, ‖fderiv ℝ (threePacketWeight φ k) y‖ ≤ H*productWaveFrequency k*threePacketWeight φ k y) := by
  sorry

end

open Set Filter Function Manifold Metric
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end
