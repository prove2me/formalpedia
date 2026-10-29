-- Prove2me | Theorems.Thm_OAI_ContingencyTables_ProfilePrograms_work_optionalTrialCount
-- name    : OAI.ContingencyTables.ProfilePrograms.work_optionalTrialCount
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:03:12.657982+00:00
-- url     : https://prove2.me/theorems/afbb542d-783e-41fb-97ba-c75e3fd3f2ff
-- title:
--   OAI.ContingencyTables.ProfilePrograms.work_optionalTrialCount: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.ProfilePrograms.work_optionalTrialCount` of [lean/OAI/Combinatorics/ContingencyTables/Sampling/OriginalTrialVector.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/OriginalTrialVector.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.ProfilePrograms`, with `open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial`):
--
--   ```lean
--   lemma work_optionalTrialCount : WorkBound optionalTrialCountRealizer optionalTrialMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.TreeTyped.instCodecBool`, `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.DensePrograms.MatrixCode` and `OAI.ContingencyTables.ProfilePrograms.ProfileCheckData` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.ProfilePrograms.ResidualParameters` and `OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited` (definitions bundle `OAIQ089A003` of this split); `OAI.MatchingFPRAS.TreeTyped.WorkBound` (definitions bundle `OAIQ089A008` of this split); `OAI.ContingencyTables.ProfilePrograms.MatrixParameters`, `OAI.ContingencyTables.ProfilePrograms.OptionalTrialInput`, `OAI.ContingencyTables.ProfilePrograms.TransitionCacheParameters`, `OAI.ContingencyTables.ProfilePrograms.WalkCountInput`, `OAI.ContingencyTables.ProfilePrograms.optionalTrialCount`, `OAI.ContingencyTables.ProfilePrograms.optionalTrialCountRealizer` and `OAI.ContingencyTables.ProfilePrograms.optionalTrialMeasure` (definitions bundle `OAIQ089A009` of this split).
--
--   **Used by.** The proof of `OAI.ContingencyTables.ProfilePrograms.work_exactMatrixInput` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/OriginalTrialVector.lean (declaration OAI.ContingencyTables.ProfilePrograms.work_optionalTrialCount)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009

section

attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma work_optionalTrialCount : WorkBound optionalTrialCountRealizer optionalTrialMeasure := by
  sorry

end ContingencyTables.ProfilePrograms

end OAI
end
