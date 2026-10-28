-- Prove2me | Theorems.Thm_OAI_Kadison_OrbitStateHull_hull_norm_separable
-- name    : OAI.Kadison.OrbitStateHull.hull_norm_separable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:57:12.317436+00:00
-- url     : https://prove2.me/theorems/76bce5a3-1f1f-42d5-aa8b-3c7c5d79def8
-- title:
--   OAI.Kadison.OrbitStateHull.hull_norm_separable: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.OrbitStateHull`, with `open Filter`, `open scoped ComplexOrder InnerProductSpace Topology`, `open PartialIsometryOrder`):
--
--   ```lean
--   theorem hull_norm_separable (x : H) :
--       TopologicalSpace.IsSeparable (WeakDual.toStrongDual '' hull M x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` and `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.PartialIsometryOrder.IsFiniteAlgebra` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.OrbitStateHull.hull` (definitions bundle `OAIQ039C039` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.uniform_commutator_separable_factor` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C039

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
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

namespace Kadison.OrbitStateHull

open PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfac hd hfin

theorem hull_norm_separable (x : H) :
    TopologicalSpace.IsSeparable (WeakDual.toStrongDual '' hull M x) := by
  sorry

end Kadison.OrbitStateHull

end

end
end

end OAI
end
