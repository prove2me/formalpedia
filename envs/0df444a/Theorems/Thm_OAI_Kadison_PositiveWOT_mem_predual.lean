-- Prove2me | Theorems.Thm_OAI_Kadison_PositiveWOT_mem_predual
-- name    : OAI.Kadison.PositiveWOT.mem_predual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:23:02.266852+00:00
-- url     : https://prove2.me/theorems/1f92e4ea-6aa7-4c2e-954c-ec4fcddbf4d4
-- title:
--   OAI.Kadison.PositiveWOT.mem_predual: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PositiveWOT`, with `open Filter`, `open scoped ComplexOrder Topology`):
--
--   ```lean
--   theorem mem_predual [TopologicalSpace.SeparableSpace H]
--       (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f) :
--       strongFunctional M f∈closure (NormalPredual.finiteTests M (TopologicalSpace.denseSeq H))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.PositiveWOT.ProjectionContinuousAtOne` (definitions bundle `OAIQ039C029` of this split); `OAI.Kadison.NormalPredual.finiteTests` and `OAI.Kadison.PositiveWOT.strongFunctional` (definitions bundle `OAIQ039C040` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.OrbitStateHull.hull_norm_separable`, `OAI_Kadison_OrbitStateHull_hull_normal` and `OAI.Kadison.uniform_commutator_separable_factor` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C040

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

open scoped ComplexOrder Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_predual [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f) :
    strongFunctional M f∈closure (NormalPredual.finiteTests M (TopologicalSpace.denseSeq H)) := by
  sorry

end Kadison.PositiveWOT

end

end
end

end OAI
end
