-- Prove2me | Theorems.Thm_OAI_SKValue_shiftedCoefficientSum_le_groundState
-- name    : OAI.SKValue.shiftedCoefficientSum_le_groundState
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:44:47.4218+00:00
-- url     : https://prove2.me/theorems/d7238665-c594-49d9-891c-a40e6cfc8d87
-- title:
--   OAI.SKValue.shiftedCoefficientSum_le_groundState: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.shiftedCoefficientSum_le_groundState` of [lean/OAI/Probability/SKValue/SKValue/GroundState/LiteralLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/GroundState/LiteralLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators`):
--
--   ```lean
--   theorem shiftedCoefficientSum_le_groundState (W : BrownianSpace) (γ : OrderParameter)
--       {T : ℝ} (hT : 0≤T) (hT1 : T<1) {N : ℕ} (hN : 0<N)
--       (hpos : ∀ j<N,0<∫ z,(rawCoefficient W γ T N j z)^2 ∂gaussianProduct (Fin (N+1))) :
--       shiftedCoefficientSum W γ T N≤groundStateValue
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.BrownianSpace`, `OAI.SKValue.OrderParameter`, `OAI.SKValue.gaussianProduct`, `OAI.SKValue.groundStateValue`, `OAI.SKValue.rawCoefficient` and `OAI.SKValue.shiftedCoefficientSum` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValue.value_consequences` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/GroundState/LiteralLower.lean (declaration OAI.SKValue.shiftedCoefficientSum_le_groundState)

import Mathlib
import Definitions.Def_SKValue

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

theorem shiftedCoefficientSum_le_groundState (W : BrownianSpace) (γ : OrderParameter)
    {T : ℝ} (hT : 0≤T) (hT1 : T<1) {N : ℕ} (hN : 0<N)
    (hpos : ∀ j<N,0<∫ z,(rawCoefficient W γ T N j z)^2 ∂gaussianProduct (Fin (N+1))) :
    shiftedCoefficientSum W γ T N≤groundStateValue := by
  sorry

end SKValue

end

end OAI
end
