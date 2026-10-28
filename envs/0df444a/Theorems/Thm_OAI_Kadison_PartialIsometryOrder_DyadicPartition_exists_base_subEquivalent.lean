-- Prove2me | Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_exists_base_subEquivalent
-- name    : OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_base_subEquivalent
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:28:44.806988+00:00
-- url     : https://prove2.me/theorems/64501306-7587-4bdb-a39e-5e8ee5a5157e
-- title:
--   OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_base_subEquivalent: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PartialIsometryOrder.DyadicPartition`, with `open scoped ComplexOrder InnerProductSpace BigOperators`):
--
--   ```lean
--   lemma exists_base_subEquivalent [TopologicalSpace.SeparableSpace H]
--       (hfin : IsFiniteAlgebra M) {e : H →L[ℂ] H}
--       (heM : e∈M) (he : IsStarProjection e) (hen : e≠0) :
--       ∃ n,SubEquivalent M (partition M hfac hd n).base e
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` and `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.PartialIsometryOrder.IsFiniteAlgebra`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.Index`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.indexFintype` and `OAI.Kadison.PartialIsometryOrder.EqualPartition` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.PartialIsometryOrder.SubEquivalent` (definitions bundle `OAIQ039C051` of this split); `OAI.Kadison.PartialIsometryOrder.DyadicPartition.partition` (definitions bundle `OAIQ039C058` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.PartialIsometryOrder.DyadicPartition.subEquivalent_of_dimension_le`, `OAI.Kadison.ProjectionDimensionTopology.vector_uniform_absolute_continuity` and `OAI.Kadison.TraceDimension.faithful` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C058

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DyadicPartition

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M)

lemma exists_base_subEquivalent [TopologicalSpace.SeparableSpace H]
    (hfin : IsFiniteAlgebra M) {e : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) (hen : e≠0) :
    ∃ n,SubEquivalent M (partition M hfac hd n).base e := by
  sorry

end DyadicPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end
