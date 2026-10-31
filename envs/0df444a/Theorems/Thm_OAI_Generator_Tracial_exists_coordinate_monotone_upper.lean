-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_coordinate_monotone_upper
-- name    : OAI.Generator.Tracial.exists_coordinate_monotone_upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T12:44:42.633666+00:00
-- url     : https://prove2.me/theorems/dd488d4e-5184-4f06-a5b2-eebc0d7ff902
-- title:
--   OAI.Generator.Tracial.exists_coordinate_monotone_upper: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_coordinate_monotone_upper` of [lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open Filter`, `open UltrapowerBridge Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem exists_coordinate_monotone_upper (hNM : N ≤ M)
--       (a : ℕ → ℕ → PartialUnitary M) (ha : ∀ j,Monotone (fun n => a n j))
--       (hN : ∀ n j,(a n j).val.val ∈ N) :
--       ∃ u : ℕ → PartialUnitary M,(∀ j,(u j).val.val ∈ N) ∧ ∀ n j,a n j ≤ u j
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.PartialUnitary` and `OAI.Generator.Tracial.PartialUnitary.val` (definitions bundle `OAIQ11Fg004` of this split); `OAI.Generator.Tracial.PartialUnitary.instPartialOrder` (definitions bundle `OAIQ11Fg012` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.exists_full_support_ordered_independence` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean (declaration OAI.Generator.Tracial.exists_coordinate_monotone_upper)

import Mathlib
import Definitions.Def_OAIQ11Fg012

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator.Tracial

open Filter

open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

include τ in
theorem exists_coordinate_monotone_upper (hNM : N ≤ M)
    (a : ℕ → ℕ → PartialUnitary M) (ha : ∀ j,Monotone (fun n => a n j))
    (hN : ∀ n j,(a n j).val.val ∈ N) :
    ∃ u : ℕ → PartialUnitary M,(∀ j,(u j).val.val ∈ N) ∧ ∀ n j,a n j ≤ u j := by
  sorry

end Generator.Tracial

end

end OAI
end
