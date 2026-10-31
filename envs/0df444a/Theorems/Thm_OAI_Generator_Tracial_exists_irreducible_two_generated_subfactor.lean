-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_irreducible_two_generated_subfactor
-- name    : OAI.Generator.Tracial.exists_irreducible_two_generated_subfactor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:41:42.771227+00:00
-- url     : https://prove2.me/theorems/c7d67d9b-36b3-4017-9589-64a0fffde163
-- title:
--   OAI.Generator.Tracial.exists_irreducible_two_generated_subfactor: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_irreducible_two_generated_subfactor` of [lean/OAI/Analysis/FactorGeneration/MatrixGenerators.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixGenerators.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge FiniteMatrixStage`):
--
--   ```lean
--   theorem exists_irreducible_two_generated_subfactor
--       (τ : TracialRepresentation M) (hNM : N ≤ M)
--       (hfactor : ∀ c : N.toStarSubalgebra,
--         (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
--       (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
--         ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
--       (hirr : ∀ c : M.toStarSubalgebra,
--         (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
--         ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
--       (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
--       ∃ P : VonNeumannAlgebra H,P ≤ N ∧ IsII1Factor P.toStarSubalgebra ∧
--         (∀ c : M.toStarSubalgebra,(∀ a : P.toStarSubalgebra,a.val*c.val=c.val*a.val) →
--           c=τ.trace c • (1 : M.toStarSubalgebra)) ∧
--         ∃ a ∈ P,∃ b ∈ P,IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=P.toStarSubalgebra
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.Generator.Tracial.coordinateInclusion` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ11Fg003` of this split); `OAI.Generator.IsII1Factor` and `OAI.Generator.wstar` (the published bundle `Def_FactorGeneration`).
--
--   **Used by.** The proofs of `OAI_Generator_Tracial_represented_four_selfAdjoint_generators` and `OAI.Generator.Tracial.singlyGenerated_of_tracialRepresentation` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixGenerators.lean (declaration OAI.Generator.Tracial.exists_irreducible_two_generated_subfactor)

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

namespace Tracial
open UltrapowerBridge FiniteMatrixStage
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem exists_irreducible_two_generated_subfactor
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ P : VonNeumannAlgebra H,P ≤ N ∧ IsII1Factor P.toStarSubalgebra ∧
      (∀ c : M.toStarSubalgebra,(∀ a : P.toStarSubalgebra,a.val*c.val=c.val*a.val) →
        c=τ.trace c • (1 : M.toStarSubalgebra)) ∧
      ∃ a ∈ P,∃ b ∈ P,IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=P.toStarSubalgebra := by
  sorry

end Tracial

end Generator

end

end OAI
end
