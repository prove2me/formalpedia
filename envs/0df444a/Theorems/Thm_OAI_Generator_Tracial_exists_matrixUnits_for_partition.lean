-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_matrixUnits_for_partition
-- name    : OAI.Generator.Tracial.exists_matrixUnits_for_partition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:35:18.696042+00:00
-- url     : https://prove2.me/theorems/5fc57814-dcd8-45a7-bb73-50b582e47fed
-- title:
--   OAI.Generator.Tracial.exists_matrixUnits_for_partition: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_matrixUnits_for_partition` of [lean/OAI/Analysis/FactorGeneration/MatrixAlgebras.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixAlgebras.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open scoped BigOperators`, `open UltrapowerBridge`):
--
--   ```lean
--   theorem exists_matrixUnits_for_partition {p : AlgebraProjection M}
--       (Q : CornerPartition p) (hn : 0 < Q.size)
--       (ht : ∀ i j, τ.trace (Q.piece i).val=τ.trace (Q.piece j).val) :
--       ∃ E : Fin Q.size → Fin Q.size → M.toStarSubalgebra,
--         (∀ i, E i i=(Q.piece i).val) ∧
--         (∀ i j, star (E i j)=E j i) ∧
--         (∀ i j k l, E i j*E k l=if j=k then E i l else 0) ∧
--         (∑ i, E i i)=p.val
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.AlgebraProjection` and `OAI.Generator.Tracial.CornerPartition` (definitions bundle `OAIQ11Fg001` of this split).
--
--   **Used by.** The proofs of `OAI.Generator.FiniteMatrixStage.exists_matrix_generated_centered_partition`, `OAI.Generator.Tracial.exists_normal_matrix_approximation`, `OAI_Generator_Tracial_exists_scalar_pinching_for_matrixUnits`, `OAI_Generator_Tracial_represented_two_selfAdjoint_generators` and `OAI.Generator.Tracial.singlyGenerated_of_tracialRepresentation` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixAlgebras.lean (declaration OAI.Generator.Tracial.exists_matrixUnits_for_partition)

import Mathlib
import Definitions.Def_OAIQ11Fg000
import Definitions.Def_OAIQ11Fg001

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

open scoped BigOperators
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include hfactor in
theorem exists_matrixUnits_for_partition {p : AlgebraProjection M}
    (Q : CornerPartition p) (hn : 0 < Q.size)
    (ht : ∀ i j, τ.trace (Q.piece i).val=τ.trace (Q.piece j).val) :
    ∃ E : Fin Q.size → Fin Q.size → M.toStarSubalgebra,
      (∀ i, E i i=(Q.piece i).val) ∧
      (∀ i j, star (E i j)=E j i) ∧
      (∀ i j k l, E i j*E k l=if j=k then E i l else 0) ∧
      (∑ i, E i i)=p.val := by
  sorry

end Tracial

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

end Generator

end

end OAI
end
