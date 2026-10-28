-- Prove2me | Theorems.Thm_OAI_Kadison_ProjectionJoin_dimension_sup_le
-- name    : OAI.Kadison.ProjectionJoin.dimension_sup_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:54:29.754828+00:00
-- url     : https://prove2.me/theorems/5563bf3a-5b00-46b8-9282-875652409080
-- title:
--   OAI.Kadison.ProjectionJoin.dimension_sup_le: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.ProjectionJoin`, with `open Filter`, `open scoped ComplexOrder InnerProductSpace Topology BigOperators`, `open PartialIsometryOrder PartialIsometryOrder.DyadicPartition`):
--
--   ```lean
--   theorem dimension_sup_le (P : ℕ → H →L[ℂ] H) (hP : ∀ n,IsStarProjection (P n))
--       (hPM : ∀ n,P n∈M) (b : ℕ → ℝ) (hb : Summable b)
--       (hPb : ∀ n,dimension M hfac hd (P n)≤b n) :
--       dimension M hfac hd (sup M P hP hPM)≤∑' n,b n
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` and `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.PartialIsometryOrder.IsFiniteAlgebra` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension` (definitions bundle `OAIQ039C058` of this split); `OAI.Kadison.ProjectionJoin.sup` (definitions bundle `OAIQ039C068` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.ProjectionDimensionTopology.vector_uniform_absolute_continuity` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C068

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

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin

theorem dimension_sup_le (P : ℕ → H →L[ℂ] H) (hP : ∀ n,IsStarProjection (P n))
    (hPM : ∀ n,P n∈M) (b : ℕ → ℝ) (hb : Summable b)
    (hPb : ∀ n,dimension M hfac hd (P n)≤b n) :
    dimension M hfac hd (sup M P hP hPM)≤∑' n,b n := by
  sorry

end Kadison.ProjectionJoin

end

end
end

end OAI
end
