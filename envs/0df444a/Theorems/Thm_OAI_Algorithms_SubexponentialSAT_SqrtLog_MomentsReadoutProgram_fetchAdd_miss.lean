-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsReadoutProgram_fetchAdd_miss
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_miss
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:12:43.339551+00:00
-- url     : https://prove2.me/theorems/19ca5674-27a4-4435-8888-ca3350b9d1bf
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_miss: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_miss` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsReadoutProgramFetch.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsReadoutProgramFetch.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram.Dictionary`):
--
--   ```lean
--   theorem fetchAdd_miss (regs : Fin 8 → Bool) (modulus width count : List Bool)
--       (entries : List (List Bool × List Bool)) (query acc : List Bool)
--       (hmiss : entries.lookup query = none) :
--       ∃ n ≤ fetchBudget entries query (7*acc.length+5), ∃ rr,
--         Eval fetchAdd n (machine regs (inputTape modulus width count entries query acc))
--           (machine rr (fetchedTape modulus width count entries query acc acc))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchedTape` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.inputTape` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.machine` (definitions bundle `OAIQ081S110` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_code` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsReadoutProgramFetch.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_miss)

import Mathlib
import Definitions.Def_OAIQ081S110

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram.Dictionary

theorem fetchAdd_miss (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (entries : List (List Bool × List Bool)) (query acc : List Bool)
    (hmiss : entries.lookup query = none) :
    ∃ n ≤ fetchBudget entries query (7*acc.length+5), ∃ rr,
      Eval fetchAdd n (machine regs (inputTape modulus width count entries query acc))
        (machine rr (fetchedTape modulus width count entries query acc acc)) := by
  sorry

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end
