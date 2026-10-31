-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_irreducible_matrix_energy_descent
-- name    : OAI.Generator.Tracial.exists_irreducible_matrix_energy_descent
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:49:18.457616+00:00
-- url     : https://prove2.me/theorems/36c2cc90-6c99-4e12-aecf-e60c8c88c798
-- title:
--   OAI.Generator.Tracial.exists_irreducible_matrix_energy_descent: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_irreducible_matrix_energy_descent` of [lean/OAI/Analysis/FactorGeneration/MatrixRefinement.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixRefinement.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open scoped BigOperators`, `open UltrapowerBridge`):
--
--   ```lean
--   theorem exists_irreducible_matrix_energy_descent (hNM : N ≤ M)
--       (hfactor : ∀ c : N.toStarSubalgebra,
--         (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
--       (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
--         ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
--       (hirr : ∀ c : M.toStarSubalgebra,
--         (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
--         ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
--       (x : M.toStarSubalgebra) (hx : x ≠ 0) (ht : τ.trace x=0) :
--       ∃ k n : ℕ,n=2^k ∧ ∃ E : MatrixUnitSystem (Fin n) N.toStarSubalgebra,
--         τ.norm₂ (conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤
--           (15/16 : ℝ)*τ.norm₂ x^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.MatrixUnitSystem`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.Generator.MatrixUnitSystem.map`, `OAI.Generator.MatrixUnitSystem.relativeVonNeumann`, `OAI.Generator.MatrixUnitSystem.relativeVonNeumann_le`, `OAI.Generator.Tracial.coordinateInclusion`, `OAI.UltrapowerBridge.TracialRepresentation.norm₂` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.conditionalExpectation` (definitions bundle `OAIQ11Fg007` of this split).
--
--   **Used by.** The proofs of `OAI.Generator.FiniteMatrixStage.exists_irreducible_matrix_generated_II1`, `OAI_Generator_FiniteMatrixStage_exists_refinement_descent`, `OAI_Generator_FiniteMatrixStage_exists_tensor_refinement_descent`, `OAI_Generator_Tracial_exists_compatible_matrix_energy_descent` and `OAI.Generator.Tracial.exists_irreducible_two_generated_subfactor` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixRefinement.lean (declaration OAI.Generator.Tracial.exists_irreducible_matrix_energy_descent)

import Mathlib
import Definitions.Def_OAIQ11Fg007

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator

namespace Tracial
open scoped BigOperators

open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N D M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_irreducible_matrix_energy_descent (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : x ≠ 0) (ht : τ.trace x=0) :
    ∃ k n : ℕ,n=2^k ∧ ∃ E : MatrixUnitSystem (Fin n) N.toStarSubalgebra,
      τ.norm₂ (conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤
        (15/16 : ℝ)*τ.norm₂ x^2 := by
  sorry

end Tracial

end Generator

end

end OAI
end
