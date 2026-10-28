-- Prove2me | Theorems.Thm_OAI_CommonBasesFPRAS_MachineCode_safe_single
-- name    : OAI.CommonBasesFPRAS.MachineCode.safe_single
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:26:44.068082+00:00
-- url     : https://prove2.me/theorems/cfc3871e-d8da-463f-8c78-3c140a85df3f
-- title:
--   OAI.CommonBasesFPRAS.MachineCode.safe_single: intermediate lemma from OpenAI, Approximate counting of common bases of two matroids
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.common_bases_fpras`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Approximate counting of common bases of two matroids*, OpenAI Math Release, September 23, 2026, result family 114, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CommonBasesFPRAS.MachineCode.safe_single` of [lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CommonBasesFPRAS.MachineCode`, with `open Expression`, `open scoped Classical`, `open Expression`, `open Expression`, `open scoped Classical`, `open Expression`, `open scoped Classical`, `open Expression`, `open Expression`, `open scoped Classical`, `open Expression`, `open scoped Classical`, `open Expression`, `open Expression Effect`, `open Expression`, `open scoped Classical`, `open Expression`, `open Expression Effect`):
--
--   ```lean
--   lemma safe_single : OracleSafe singleCode (bankScope algorithmScope)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.MachineCode.AlgorithmParams`, `OAI.CommonBasesFPRAS.MachineCode.BankData`, `OAI.CommonBasesFPRAS.MachineCode.OracleSafe`, `OAI.CommonBasesFPRAS.MachineCode.DataType`, `OAI.CommonBasesFPRAS.MachineCode.Effect.algorithmScope`, `OAI.CommonBasesFPRAS.MachineCode.Effect.bankScope`, `OAI.CommonBasesFPRAS.MachineCode.Expression.NN` and `OAI.CommonBasesFPRAS.MachineCode.Expression.singleCode` (definitions bundle `OAIQ2Mt000` of this split).
--
--   **Used by.** The proof of `OAI.CommonBasesFPRAS.MachineCode.frozen_uniform_safe` of this split imports it.
-- source:
--   OpenAI, Approximate counting of common bases of two matroids, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 114; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Approximate-counting-of-common-bases-of-two-matroids-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean (declaration OAI.CommonBasesFPRAS.MachineCode.safe_single)

import Mathlib
import Definitions.Def_OAIQ2Mt000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

namespace MachineCode


open Expression

open Expression

open Expression

open Expression

open Expression

open Expression
end MachineCode

namespace MachineCode

open Expression
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression
open scoped Classical

open Expression

open Expression Effect

open Expression
open scoped Classical

open Expression

open Expression Effect
lemma safe_single : OracleSafe singleCode (bankScope algorithmScope) := by
  sorry

open Expression
open Expression Effect

open Expression

open Expression

open Expression Effect

open Expression

open Expression

open Expression Effect
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression

open scoped Classical

end MachineCode
end CommonBasesFPRAS

open CommonBasesFPRAS CommonBasesFPRAS.MachineCode

end OAI
end
