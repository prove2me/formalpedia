-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_predual_small_of_small_trace_sandwich_q129
-- name    : OAI.Generator.Tracial.predual_small_of_small_trace_sandwich_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:19:52.804835+00:00
-- url     : https://prove2.me/theorems/62c67106-0c1f-4ce7-8ce3-f4f53f72f930
-- title:
--   OAI.Generator.Tracial.predual_small_of_small_trace_sandwich_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.predual_small_of_small_trace_sandwich` of [lean/OAI/Analysis/FactorGeneration/PredualContinuity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PredualContinuity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open Filter`, `open scoped Topology`, `open UltrapowerBridge`):
--
--   ```lean
--   theorem predual_small_of_small_trace_sandwich_q129 (x : X) (ε : ℝ) (hε : 0 < ε) :
--       ∃ δ : ℝ, 0 < δ ∧ ∀ a p : M.toStarSubalgebra,
--         0 ≤ p.val → ‖p‖ ≤ 1 → (τ.trace p).re < δ →
--         -p.val ≤ a.val → a.val ≤ p.val →
--         ‖predualFunctional M.toStarSubalgebra e x a‖ < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.predualFunctional`, `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ129G001` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.traceOrbit_isSeparable_of_separablePredual_q129` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PredualContinuity.lean (declaration OAI.Generator.Tracial.predual_small_of_small_trace_sandwich)

import Mathlib
import Definitions.Def_OAIQ129G001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator.Tracial

section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra)

theorem predual_small_of_small_trace_sandwich_q129 (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a p : M.toStarSubalgebra,
      0 ≤ p.val → ‖p‖ ≤ 1 → (τ.trace p).re < δ →
      -p.val ≤ a.val → a.val ≤ p.val →
      ‖predualFunctional M.toStarSubalgebra e x a‖ < ε := by
  sorry

end

open UltrapowerBridge

end Generator.Tracial

end

end OAI
end
