-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_commuting_matrix_extension_q129
-- name    : OAI.Generator.Tracial.exists_commuting_matrix_extension_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:18:34.110455+00:00
-- url     : https://prove2.me/theorems/6092daf0-3b41-4728-b0cf-e5241d4fdf65
-- title:
--   OAI.Generator.Tracial.exists_commuting_matrix_extension_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_commuting_matrix_extension` of [lean/OAI/Analysis/FactorGeneration/MatrixRefinement.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixRefinement.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge`):
--
--   ```lean
--   theorem exists_commuting_matrix_extension_q129
--       (τ : TracialRepresentation M) (E : MatrixUnitSystem ι M.toStarSubalgebra) (o : ι)
--       (hfactor : ∀ c : M.toStarSubalgebra,
--         (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
--       (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
--         ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
--       (n : ℕ) (hn : 0 < n) :
--       ∃ F : MatrixUnitSystem (Fin n) M.toStarSubalgebra,
--         ∃ hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l),
--           Function.Injective F.hom ∧
--           (∀ j,τ.trace (F.entry j j)=(((n : ℝ)⁻¹ : ℝ) : ℂ)) ∧
--           E.algebra ≤ (E.product F hc).algebra ∧
--           WOTClosed (E.product F hc).concreteAlgebra
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.MatrixUnitSystem`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.Generator.MatrixUnitSystem.algebra`, `OAI.Generator.MatrixUnitSystem.concreteAlgebra`, `OAI.Generator.MatrixUnitSystem.hom`, `OAI.Generator.MatrixUnitSystem.product` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ129G001` of this split); `OAI.Generator.WOTClosed` (the published bundle `Def_FactorGeneration`).
--
--   **Used by.** The proofs of `OAI_Generator_Tracial_exists_residual_quotient_increment_q129`, `OAI.Generator.Tracial.exists_scalar_pinching_for_matrixUnits_q129` and `OAI.Generator.single_generation_of_II1_separable_predual` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixRefinement.lean (declaration OAI.Generator.Tracial.exists_commuting_matrix_extension)

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ129G001

section

attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator

namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_commuting_matrix_extension_q129
    (τ : TracialRepresentation M) (E : MatrixUnitSystem ι M.toStarSubalgebra) (o : ι)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (n : ℕ) (hn : 0 < n) :
    ∃ F : MatrixUnitSystem (Fin n) M.toStarSubalgebra,
      ∃ hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l),
        Function.Injective F.hom ∧
        (∀ j,τ.trace (F.entry j j)=(((n : ℝ)⁻¹ : ℝ) : ℂ)) ∧
        E.algebra ≤ (E.product F hc).algebra ∧
        WOTClosed (E.product F hc).concreteAlgebra := by
  sorry

end Tracial

end Generator

end

end OAI
end
