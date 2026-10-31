-- Prove2me | Theorems.Thm_OAI_Generator_FiniteMatrixStage_generated_isII1
-- name    : OAI.Generator.FiniteMatrixStage.generated_isII1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:36:12.986198+00:00
-- url     : https://prove2.me/theorems/9f08e870-cc28-4da1-95d8-8db2c40b7629
-- title:
--   OAI.Generator.FiniteMatrixStage.generated_isII1: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.FiniteMatrixStage.generated_isII1` of [lean/OAI/Analysis/FactorGeneration/MatrixSequence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixSequence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.FiniteMatrixStage`, with `open UltrapowerBridge Tracial`):
--
--   ```lean
--   theorem generated_isII1 (A : ℕ → FiniteMatrixStage N)
--       (τ : TracialRepresentation M) (hNM : N ≤ M)
--       (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
--         ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
--       (hirr : ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
--         c=τ.trace c • (1 : M.toStarSubalgebra)) : IsII1Factor (generated A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.FiniteMatrixStage`, `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.FiniteMatrixStage.generated` (definitions bundle `OAIQ11Fg003` of this split); `OAI.Generator.IsII1Factor` (the published bundle `Def_FactorGeneration`).
--
--   **Used by.** The proofs of `OAI.Generator.FiniteMatrixStage.exists_irreducible_matrix_generated_II1`, `OAI_Generator_Tracial_exists_irreducible_centered_partition` and `OAI.Generator.Tracial.exists_irreducible_two_generated_subfactor` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixSequence.lean (declaration OAI.Generator.FiniteMatrixStage.generated_isII1)

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ11Fg003

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem generated_isII1 (A : ℕ → FiniteMatrixStage N)
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
      c=τ.trace c • (1 : M.toStarSubalgebra)) : IsII1Factor (generated A) := by
  sorry

end FiniteMatrixStage

end

end Generator

end

end OAI
end
