-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_CornerPartition_block_commutant_mem_subalgebra
-- name    : OAI.Generator.Tracial.CornerPartition.block_commutant_mem_subalgebra
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:40:07.626872+00:00
-- url     : https://prove2.me/theorems/e12fd206-bd6b-4f87-9f6b-54ceefcc22ac
-- title:
--   OAI.Generator.Tracial.CornerPartition.block_commutant_mem_subalgebra: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.CornerPartition.block_commutant_mem_subalgebra` of [lean/OAI/Analysis/FactorGeneration/Subfactors.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Subfactors.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial.CornerPartition`, with `open scoped BigOperators`, `open UltrapowerBridge`):
--
--   ```lean
--   theorem block_commutant_mem_subalgebra
--       (hN : ∀ i, (Q.piece i).val.val ∈ N)
--       (hirr : ∀ c : M.toStarSubalgebra,
--         (∀ a : insideAlgebra (M := M) (P := N),
--           (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
--         ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
--       (c : M.toStarSubalgebra)
--       (hc : ∀ a : insideAlgebra (M := M) (P := Q.blockVonNeumann N),
--         (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) : c.val ∈ N
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.CornerPartition`, `OAI.Generator.Tracial.identityProjection` and `OAI.Generator.Tracial.insideAlgebra` (definitions bundle `OAIQ11Fg001` of this split); `OAI.Generator.Tracial.CornerPartition.blockVonNeumann` (definitions bundle `OAIQ11Fg005` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Subfactors.lean (declaration OAI.Generator.Tracial.CornerPartition.block_commutant_mem_subalgebra)

import Mathlib
import Definitions.Def_OAIQ11Fg000
import Definitions.Def_OAIQ11Fg005

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator.Tracial

section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace CornerPartition
variable (Q : CornerPartition (identityProjection M))

include τ in
theorem block_commutant_mem_subalgebra
    (hN : ∀ i, (Q.piece i).val.val ∈ N)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := N),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (c : M.toStarSubalgebra)
    (hc : ∀ a : insideAlgebra (M := M) (P := Q.blockVonNeumann N),
      (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) : c.val ∈ N := by
  sorry

end CornerPartition

end

open UltrapowerBridge

end Generator.Tracial

end

end OAI
end
