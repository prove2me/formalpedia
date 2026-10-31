-- Prove2me | Theorems.Thm_OAI_Generator_FiniteMatrixStage_exists_irreducible_matrix_generated_II1
-- name    : OAI.Generator.FiniteMatrixStage.exists_irreducible_matrix_generated_II1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:37:48.752497+00:00
-- url     : https://prove2.me/theorems/788cc321-099e-4857-835a-29fe08044aa9
-- title:
--   OAI.Generator.FiniteMatrixStage.exists_irreducible_matrix_generated_II1: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.FiniteMatrixStage.exists_irreducible_matrix_generated_II1` of [lean/OAI/Analysis/FactorGeneration/MatrixSequence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixSequence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.FiniteMatrixStage`, with `open UltrapowerBridge Tracial`):
--
--   ```lean
--   theorem exists_irreducible_matrix_generated_II1
--       (τ : TracialRepresentation M) (hNM : N ≤ M)
--       (hfactor : ∀ c : N.toStarSubalgebra,
--         (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
--       (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
--         ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
--       (hirr : ∀ c : M.toStarSubalgebra,
--         (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
--         ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
--       (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
--       ∃ A : ℕ → FiniteMatrixStage N,A 0=scalarStage N ∧
--         Monotone (fun n => (A n).units.concreteAlgebra) ∧
--         (∀ n,FiniteDimensional ℂ (A n).units.concreteAlgebra) ∧
--         IsII1Factor (generated A) ∧ generated A ≤ N.toStarSubalgebra ∧
--         ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
--           c=τ.trace c • (1 : M.toStarSubalgebra)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.FiniteMatrixStage`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.Generator.Tracial.coordinateInclusion` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.FiniteMatrixStage.generated`, `OAI.Generator.FiniteMatrixStage.scalarStage`, `OAI.Generator.MatrixUnitSystem.concreteAlgebra` and `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ11Fg003` of this split); `OAI.Generator.IsII1Factor` (the published bundle `Def_FactorGeneration`).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.exists_unitResidual_local_compression` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixSequence.lean (declaration OAI.Generator.FiniteMatrixStage.exists_irreducible_matrix_generated_II1)

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

theorem exists_irreducible_matrix_generated_II1
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ A : ℕ → FiniteMatrixStage N,A 0=scalarStage N ∧
      Monotone (fun n => (A n).units.concreteAlgebra) ∧
      (∀ n,FiniteDimensional ℂ (A n).units.concreteAlgebra) ∧
      IsII1Factor (generated A) ∧ generated A ≤ N.toStarSubalgebra ∧
      ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
        c=τ.trace c • (1 : M.toStarSubalgebra) := by
  sorry

end FiniteMatrixStage

end

end Generator

end

end OAI
end
