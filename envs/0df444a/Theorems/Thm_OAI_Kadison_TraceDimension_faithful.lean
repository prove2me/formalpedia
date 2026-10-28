-- Prove2me | Theorems.Thm_OAI_Kadison_TraceDimension_faithful
-- name    : OAI.Kadison.TraceDimension.faithful
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:38:14.953025+00:00
-- url     : https://prove2.me/theorems/4218cf7b-cacc-4210-b947-e10609abc561
-- title:
--   OAI.Kadison.TraceDimension.faithful: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TraceDimension`, with `open Filter`, `open scoped ComplexOrder InnerProductSpace Topology`, `open PartialIsometryOrder PartialIsometryOrder.DyadicPartition`):
--
--   ```lean
--   theorem faithful (a : M) (hzero : τ (star a*a)=0) : a=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` and `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.PartialIsometryOrder.IsFiniteAlgebra` (definitions bundle `OAIQ039C015` of this split).
--
--   **Used by.** The proofs of `OAI_Kadison_OrbitStateHull_exists_faithful_normal_trace` and `OAI.Kadison.uniform_commutator_separable_factor` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C015

section

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

namespace Kadison.TraceDimension

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable (hfac : FactorCorner.IsFactor M) (hd : DiffuseProjection.HasNoMinimalProjections M)

variable (hfin : IsFiniteAlgebra M) (hone : τ 1=1)

include hτ hfac hd hfin hone

theorem faithful (a : M) (hzero : τ (star a*a)=0) : a=0 := by
  sorry

end Kadison.TraceDimension

end

end
end

end OAI
end
