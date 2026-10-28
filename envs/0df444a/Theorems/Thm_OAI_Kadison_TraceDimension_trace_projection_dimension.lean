-- Prove2me | Theorems.Thm_OAI_Kadison_TraceDimension_trace_projection_dimension
-- name    : OAI.Kadison.TraceDimension.trace_projection_dimension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:30:39.363019+00:00
-- url     : https://prove2.me/theorems/0b2ab575-8324-4c57-a617-43a4ebd5468c
-- title:
--   OAI.Kadison.TraceDimension.trace_projection_dimension: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TraceDimension`, with `open Filter`, `open scoped ComplexOrder InnerProductSpace Topology BigOperators`, `open PartialIsometryOrder PartialIsometryOrder.DyadicPartition`):
--
--   ```lean
--   theorem trace_projection_dimension [Nontrivial H] (hfin : IsFiniteAlgebra M)
--       (hone : τ 1=1) {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) :
--       (τ ⟨e,heM⟩).re=dimension M hfac hd e
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` and `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.PartialIsometryOrder.IsFiniteAlgebra` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension` (definitions bundle `OAIQ039C058` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TraceDimension.faithful` of this split imports it.
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

open Filter

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.TraceDimension

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

include hτ

variable (hfac : FactorCorner.IsFactor M) (hd : DiffuseProjection.HasNoMinimalProjections M)

theorem trace_projection_dimension [Nontrivial H] (hfin : IsFiniteAlgebra M)
    (hone : τ 1=1) {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) :
    (τ ⟨e,heM⟩).re=dimension M hfac hd e := by
  sorry

end Kadison.TraceDimension

end

end
end

end OAI
end
