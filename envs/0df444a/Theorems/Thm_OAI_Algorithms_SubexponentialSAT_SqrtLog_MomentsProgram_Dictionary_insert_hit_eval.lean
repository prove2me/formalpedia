-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Dictionary_insert_hit_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_hit_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:11:58.344192+00:00
-- url     : https://prove2.me/theorems/514f8052-6004-448d-a974-535a4feae2b2
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_hit_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_hit_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramDictionaryInsert.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramDictionaryInsert.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem insert_hit_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
--       (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
--       (regs : Fin 8 → Bool) (width count : List Bool)
--       (entries : List (List Bool × List Bool)) (query : List Bool)
--       (hhit : entries.lookup query = some (RingScan.rightBits pairs))
--       (hc : count.length = pairs.length) (hw : width.length = baseWidth p t) :
--       ∃ n ≤ insertBudget entries query (RingScan.sumBits p t M pairs) (hitBudget p t pairs), ∃ rr,
--         Eval insert n (machine regs (inputTape M.bits width count entries query (RingScan.leftBits pairs)))
--           (machine rr (outputTape M.bits width count
--             (updatedBytes entries query (RingScan.sumBits p t M pairs)) (RingScan.leftBits pairs)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insertBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.updatedBytes` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.outputTape` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.leftBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.rightBits` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.sumBits` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.inputTape` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.hitBudget` (definitions bundle `OAIQ081S077` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.machine` (definitions bundle `OAIQ081S110` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_code_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramDictionaryInsert.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_hit_eval)

import Mathlib
import Definitions.Def_OAIQ081S110

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem insert_hit_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (width count : List Bool)
    (entries : List (List Bool × List Bool)) (query : List Bool)
    (hhit : entries.lookup query = some (RingScan.rightBits pairs))
    (hc : count.length = pairs.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ insertBudget entries query (RingScan.sumBits p t M pairs) (hitBudget p t pairs), ∃ rr,
      Eval insert n (machine regs (inputTape M.bits width count entries query (RingScan.leftBits pairs)))
        (machine rr (outputTape M.bits width count
          (updatedBytes entries query (RingScan.sumBits p t M pairs)) (RingScan.leftBits pairs))) := by
  sorry

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end
