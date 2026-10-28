-- Prove2me | Theorems.Thm_OAI_Kadison_CentralAverage_exists_finite_average
-- name    : OAI.Kadison.CentralAverage.exists_finite_average
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:20:02.233232+00:00
-- url     : https://prove2.me/theorems/62b6828a-d21c-46f9-b787-2630b4276629
-- title:
--   OAI.Kadison.CentralAverage.exists_finite_average: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CentralAverage`, with `open scoped InnerProductSpace`, `open UnitaryOrbit`):
--
--   ```lean
--   theorem exists_finite_average (Y : H →L[ℂ] H) (s : Finset (CentralProjection M)) :
--       ∃ T : H →L[ℂ] H,T∈hull M Y ∧ ∀ p∈s,T*p.val=p.val*T
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CentralAverage.CentralProjection` (definitions bundle `OAIQ039C001` of this split); `OAI.Kadison.UnitaryOrbit.hull` (definitions bundle `OAIQ039C030` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.CentralAverage.exists_center_average` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C001
import Definitions.Def_OAIQ039C030

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

open scoped InnerProductSpace

namespace Kadison.CentralAverage

open UnitaryOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

theorem exists_finite_average (Y : H →L[ℂ] H) (s : Finset (CentralProjection M)) :
    ∃ T : H →L[ℂ] H,T∈hull M Y ∧ ∀ p∈s,T*p.val=p.val*T := by
  sorry

end Kadison.CentralAverage

end

end
end

end OAI
end
