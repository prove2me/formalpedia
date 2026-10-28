-- Prove2me | Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_dimension_base
-- name    : OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_base
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:26:37.644081+00:00
-- url     : https://prove2.me/theorems/bfa7ceb9-8173-48cc-a19d-134900c1764a
-- title:
--   OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_base: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PartialIsometryOrder.DyadicPartition`, with `open scoped ComplexOrder InnerProductSpace Topology BigOperators`):
--
--   ```lean
--   lemma dimension_base (n : ℕ) :
--       dimension M hfac hd (partition M hfac hd n).base=(1:ℝ)/2^n
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` and `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.PartialIsometryOrder.IsFiniteAlgebra`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.Index`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.indexFintype` and `OAI.Kadison.PartialIsometryOrder.EqualPartition` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension` and `OAI.Kadison.PartialIsometryOrder.DyadicPartition.partition` (definitions bundle `OAIQ039C058` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_tendsto_of_strong_increasing` of this split imports it.
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

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin in
lemma dimension_base (n : ℕ) :
    dimension M hfac hd (partition M hfac hd n).base=(1:ℝ)/2^n := by
  sorry

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
end
