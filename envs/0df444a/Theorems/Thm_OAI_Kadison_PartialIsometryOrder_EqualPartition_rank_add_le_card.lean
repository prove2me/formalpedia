-- Prove2me | Theorems.Thm_OAI_Kadison_PartialIsometryOrder_EqualPartition_rank_add_le_card
-- name    : OAI.Kadison.PartialIsometryOrder.EqualPartition.rank_add_le_card
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:23:54.600032+00:00
-- url     : https://prove2.me/theorems/57b4d3ba-7137-4ef6-8f42-7a9ff9f55215
-- title:
--   OAI.Kadison.PartialIsometryOrder.EqualPartition.rank_add_le_card: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PartialIsometryOrder.EqualPartition`, with `open scoped ComplexOrder InnerProductSpace BigOperators`):
--
--   ```lean
--   lemma rank_add_le_card (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
--       {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
--       (he : IsStarProjection e) (hf : IsStarProjection f) (hef : e*f=0) :
--       D.rank e+D.rank f ≤ Fintype.card ι
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.PartialIsometryOrder.EqualPartition` and `OAI.Kadison.PartialIsometryOrder.IsFiniteAlgebra` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.PartialIsometryOrder.EqualPartition.rank` (definitions bundle `OAIQ039C051` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.PartialIsometryOrder.DyadicPartition.lower_orthogonal_add_le` of this split imports it.
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

variable [Nontrivial H]

lemma rank_add_le_card (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : e*f=0) :
    D.rank e+D.rank f ≤ Fintype.card ι := by
  sorry

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end
