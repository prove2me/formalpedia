-- Prove2me | Theorems.Thm_OAI_Kadison_PartialIsometryOrder_EqualPartition_card_le_of_part_subEquivalent
-- name    : OAI.Kadison.PartialIsometryOrder.EqualPartition.card_le_of_part_subEquivalent
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:24:52.237468+00:00
-- url     : https://prove2.me/theorems/a366e160-1347-4b27-9bf5-32588f5a7591
-- title:
--   OAI.Kadison.PartialIsometryOrder.EqualPartition.card_le_of_part_subEquivalent: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PartialIsometryOrder.EqualPartition`, with `open scoped ComplexOrder InnerProductSpace BigOperators`):
--
--   ```lean
--   lemma card_le_of_part_subEquivalent [Nontrivial H] (hfin : IsFiniteAlgebra M)
--       (s t : Finset ι) (h : SubEquivalent M (D.part s) (D.part t)) : s.card≤t.card
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.PartialIsometryOrder.EqualPartition`, `OAI.Kadison.PartialIsometryOrder.IsFiniteAlgebra` and `OAI.Kadison.PartialIsometryOrder.EqualPartition.part` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.PartialIsometryOrder.SubEquivalent` (definitions bundle `OAIQ039C051` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_base`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.lower_orthogonal_add_upper`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.subEquivalent_of_dimension_le`, `OAI.Kadison.PartialIsometryOrder.EqualPartition.rank_add_le_card`, `OAI.Kadison.ProjectionDimensionTopology.vector_uniform_absolute_continuity`, `OAI.Kadison.ProjectionJoin.dimension_finiteJoin_le` and `OAI.Kadison.TraceDimension.faithful` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C051

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

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

lemma card_le_of_part_subEquivalent [Nontrivial H] (hfin : IsFiniteAlgebra M)
    (s t : Finset ι) (h : SubEquivalent M (D.part s) (D.part t)) : s.card≤t.card := by
  sorry

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end
