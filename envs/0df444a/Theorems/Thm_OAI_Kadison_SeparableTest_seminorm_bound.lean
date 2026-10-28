-- Prove2me | Theorems.Thm_OAI_Kadison_SeparableTest_seminorm_bound
-- name    : OAI.Kadison.SeparableTest.seminorm_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:21:57.481885+00:00
-- url     : https://prove2.me/theorems/fb69b166-ba13-4af0-b8b8-8588ffd95040
-- title:
--   OAI.Kadison.SeparableTest.seminorm_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.SeparableTest`, with `open scoped InnerProductSpace BigOperators`, `open SeparableReducingHull ReducingRepresentation`):
--
--   ```lean
--   lemma seminorm_bound (P : VonNeumannAlgebra H) (hX : ∀ i j,X i j∈P) :
--       commutatorSeminorm (NormalGNS.bicommutant (representation h X Y ξ).range) (restrictedY h X Y ξ)≤
--         commutatorSeminorm P Y
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.bicommutant` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.SeparableTest.algebra` and `OAI.Kadison.SeparableTest.space` (definitions bundle `OAIQ039C017` of this split); `OAI.Kadison.SeparableTest.representation`, `OAI.Kadison.SeparableTest.restrictedY` and `OAI.Kadison.SeparableTest.space_complete` (definitions bundle `OAIQ039C030` of this split); `OAI.Kadison.commutatorSeminorm` (the published bundle `Def_UniformCommutator`).
--
--   **Used by.** The proof of `OAI.Kadison.SeparableTest.bound_of_separable_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C011
import Definitions.Def_OAIQ039C030

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.SeparableTest

open SeparableReducingHull ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (Y : H →L[ℂ] H)

variable (ξ : PiLp 2 (fun _ : Fin h => H))

lemma seminorm_bound (P : VonNeumannAlgebra H) (hX : ∀ i j,X i j∈P) :
    commutatorSeminorm (NormalGNS.bicommutant (representation h X Y ξ).range) (restrictedY h X Y ξ)≤
      commutatorSeminorm P Y := by
  sorry

end Kadison.SeparableTest

end

end
end

end OAI
end
