-- Prove2me | Theorems.Thm_OAI_ContingencyTables_CompanionObservedUpdateProgram_polynomial_output
-- name    : OAI.ContingencyTables.CompanionObservedUpdateProgram.polynomial_output
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T03:16:33.667002+00:00
-- url     : https://prove2.me/theorems/760932cd-d9d4-4dc4-bd7c-daed49e179eb
-- title:
--   OAI.ContingencyTables.CompanionObservedUpdateProgram.polynomial_output: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.CompanionObservedUpdateProgram.polynomial_output` of [lean/OAI/Combinatorics/ContingencyTables/Counting/CompanionObservedUpdateProgram.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CompanionObservedUpdateProgram.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.CompanionObservedUpdateProgram`, with `open MatchingFPRAS MatchingFPRAS.TreeTyped`):
--
--   ```lean
--   lemma polynomial_output : PolynomialTime outputRealizer
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.CompanionMultiplierMatrixProgram.FractionMatrix`, `OAI.ContingencyTables.CompanionPhaseFinishProgram.Fraction`, `OAI.ContingencyTables.CompanionPhaseFinishProgram.Stored` and `OAI.MatchingFPRAS.TreeFraction.Fraction` (definitions bundle `OAIQ089A001` of this split); `OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited` (definitions bundle `OAIQ089A003` of this split); `OAI.ContingencyTables.CompanionObservedUpdateProgram.Input`, `OAI.ContingencyTables.CompanionObservedUpdateProgram.instCodecInput`, `OAI.ContingencyTables.CompanionObservedUpdateProgram.output` and `OAI.ContingencyTables.CompanionObservedUpdateProgram.outputRealizer` (definitions bundle `OAIQ089A006` of this split); `OAI.MatchingFPRAS.TreeTyped.PolynomialTime` (definitions bundle `OAIQ089A008` of this split).
--
--   **Used by.** The proof of `OAI.ContingencyTables.CompanionPhaseTrialProgram.polynomial_output` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CompanionObservedUpdateProgram.lean (declaration OAI.ContingencyTables.CompanionObservedUpdateProgram.polynomial_output)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A006
import Definitions.Def_OAIQ089A008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.CompanionObservedUpdateProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

attribute [local irreducible] queryInput

attribute [local irreducible] finishInput

attribute [local instance] OAI.ContingencyTables.CompanionObservedUpdateProgram.instCodecConfigs
attribute [local instance] OAI.ContingencyTables.CompanionObservedUpdateProgram.instCodecBase
attribute [local instance] OAI.ContingencyTables.CompanionObservedUpdateProgram.instCodecProdConfigsBase
attribute [local instance] OAI.ContingencyTables.CompanionObservedUpdateProgram.instCodecInput
lemma polynomial_output : PolynomialTime outputRealizer := by
  sorry

end ContingencyTables.CompanionObservedUpdateProgram

end OAI
end
