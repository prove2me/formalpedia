-- Prove2me | Theorems.Thm_OAI_ContingencyTables_ProfilePrograms_work_exactMatrixInput
-- name    : OAI.ContingencyTables.ProfilePrograms.work_exactMatrixInput
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:03:09.545643+00:00
-- url     : https://prove2.me/theorems/143333d7-0aaa-4ba6-9b38-290b7c77d118
-- title:
--   OAI.ContingencyTables.ProfilePrograms.work_exactMatrixInput: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.ProfilePrograms.work_exactMatrixInput` of [lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactResidualInput.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactResidualInput.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.ProfilePrograms`, with `open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial`):
--
--   ```lean
--   lemma work_exactMatrixInput : WorkBound exactMatrixInputRealizer exactRareMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.DensePrograms.MatrixCode` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.DensePrograms.CompletionMargins` (definitions bundle `OAIQ089A002` of this split); `OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited` (definitions bundle `OAIQ089A003` of this split); `OAI.ContingencyTables.ExactMatrixTrial.Input` and `OAI.ContingencyTables.ExactMatrixTrial.Lookup` (definitions bundle `OAIQ089A004` of this split); `OAI.MatchingFPRAS.TreeTyped.WorkBound` (definitions bundle `OAIQ089A008` of this split); `OAI.ContingencyTables.ProfilePrograms.exactMatrixInput`, `OAI.ContingencyTables.ProfilePrograms.exactMatrixInputRealizer` and `OAI.ContingencyTables.ProfilePrograms.exactRareMeasure` (definitions bundle `OAIQ089A009` of this split).
--
--   **Used by.** The proof of `OAI.ContingencyTables.SmallGraphProfiles.exact_public_correction_bound` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactResidualInput.lean (declaration OAI.ContingencyTables.ProfilePrograms.work_exactMatrixInput)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] exactResidualInput scheduledResidualCounts originalCandidates

attribute [local irreducible] exactRareWeights

lemma work_exactMatrixInput : WorkBound exactMatrixInputRealizer exactRareMeasure := by
  sorry

end ContingencyTables.ProfilePrograms

end OAI
end
