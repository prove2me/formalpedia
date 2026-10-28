-- Prove2me | Theorems.Thm_OAI_Kadison_ProjectionDimensionTopology_vector_uniform_absolute_continuity
-- name    : OAI.Kadison.ProjectionDimensionTopology.vector_uniform_absolute_continuity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:29:47.712516+00:00
-- url     : https://prove2.me/theorems/e4db0d45-81b4-4ae8-863c-72f28664a967
-- title:
--   OAI.Kadison.ProjectionDimensionTopology.vector_uniform_absolute_continuity: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.ProjectionDimensionTopology`, with `open Filter`, `open scoped ComplexOrder InnerProductSpace Topology`, `open PartialIsometryOrder PartialIsometryOrder.DyadicPartition ProjectionJoin`):
--
--   ```lean
--   theorem vector_uniform_absolute_continuity (x : H) (ε : ℝ) (hε : 0<ε) :
--       ∃ δ : ℝ,0<δ ∧ ∀ p : H →L[ℂ] H,p∈M → IsStarProjection p →
--         dimension M hfac hd p<δ → ‖p x‖<ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` and `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.PartialIsometryOrder.IsFiniteAlgebra` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension` (definitions bundle `OAIQ039C058` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.OrbitStateHull.hull_projectionContinuousAtOne` of this split imports it.
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

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.ProjectionDimensionTopology

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin

theorem vector_uniform_absolute_continuity (x : H) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ p : H →L[ℂ] H,p∈M → IsStarProjection p →
      dimension M hfac hd p<δ → ‖p x‖<ε := by
  sorry

end Kadison.ProjectionDimensionTopology

end

end
end

end OAI
end
