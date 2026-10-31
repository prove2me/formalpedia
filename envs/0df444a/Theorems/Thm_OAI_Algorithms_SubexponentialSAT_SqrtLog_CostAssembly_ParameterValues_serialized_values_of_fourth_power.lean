-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_ParameterValues_serialized_values_of_fourth_power
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.serialized_values_of_fourth_power
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:24:29.292512+00:00
-- url     : https://prove2.me/theorems/4645c7d7-ac62-41e4-a65e-1249ea2dbfda
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.serialized_values_of_fourth_power: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.serialized_values_of_fourth_power` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CostAssemblyParameterValues.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CostAssemblyParameterValues.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues`, with `open LeafParametersProgram LeafParametersProgram.Bank LeafParametersProgram.Circuit`):
--
--   ```lean
--   theorem serialized_values_of_fourth_power : ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ)
--       (n : ℕ), magnitude x ≤ n^4 → ∀ j,
--       (result Serialization.code (Execute.guardedModel x l)).val j ≤ C*(n+1)^d
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.Model` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Input` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.magnitude` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.result` (definitions bundle `OAIQ081S067` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.code` (definitions bundle `OAIQ081S153` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_scalar_input_cap_of_scope_resources` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CostAssemblyParameterValues.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.serialized_values_of_fourth_power)

import Mathlib
import Definitions.Def_OAIQ081S153

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

open LeafParametersProgram LeafParametersProgram.Bank LeafParametersProgram.Circuit

theorem serialized_values_of_fourth_power : ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ)
    (n : ℕ), magnitude x ≤ n^4 → ∀ j,
    (result Serialization.code (Execute.guardedModel x l)).val j ≤ C*(n+1)^d := by
  sorry

end SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

end OAI.Algorithms
end
