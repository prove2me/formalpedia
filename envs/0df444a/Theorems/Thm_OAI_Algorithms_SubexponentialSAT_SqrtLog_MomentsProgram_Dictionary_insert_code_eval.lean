-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Dictionary_insert_code_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_code_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:35:29.90523+00:00
-- url     : https://prove2.me/theorems/0cf0e6ed-9cae-483c-844b-1a0b9a7cdc95
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_code_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_code_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramDictionaryCode.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramDictionaryCode.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem insert_code_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
--       (cache : RingProgram.ScalarCache p t) {d : ℕ}
--       (key : K → List Bool) (hk : Function.Injective key)
--       (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
--       (x : RingProgram.Code (Word (baseWidth p t)) d)
--       (regs : Fin 8 → Bool) (width count : List Bool)
--       (hc : count.length = d) (hw : width.length = baseWidth p t) :
--       let encoded := Squarefree.Program.encodeDictionary key RingProgram.flat entries
--       let value := match entries.lookup k with
--         | none => x
--         | some y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1
--       ∃ n ≤ insertBudget encoded (key k) (RingProgram.flat value) (codeBranchBudget (baseWidth p t) d),
--       ∃ rr, Eval insert n (machine regs (inputTape M.bits width count encoded (key k) (RingProgram.flat x)))
--         (machine rr (outputTape M.bits width count
--           (Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key RingProgram.flat
--             (insertCode p t M cache k x entries))) (RingProgram.flat x)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.codeBranchBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.encodeDictionary` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.addRun` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insertBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.rawEntries` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.outputTape` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.inputTape` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.scalarProgram` (definitions bundle `OAIQ081S068` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.machine` (definitions bundle `OAIQ081S110` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insertCode` (definitions bundle `OAIQ081S119` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramDictionaryCode.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_code_eval)

import Mathlib
import Definitions.Def_OAIQ081S110
import Definitions.Def_OAIQ081S119

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

variable {K : Type*} [DecidableEq K]

theorem insert_code_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (key : K → List Bool) (hk : Function.Injective key)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (regs : Fin 8 → Bool) (width count : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p t) :
    let encoded := Squarefree.Program.encodeDictionary key RingProgram.flat entries
    let value := match entries.lookup k with
      | none => x
      | some y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1
    ∃ n ≤ insertBudget encoded (key k) (RingProgram.flat value) (codeBranchBudget (baseWidth p t) d),
    ∃ rr, Eval insert n (machine regs (inputTape M.bits width count encoded (key k) (RingProgram.flat x)))
      (machine rr (outputTape M.bits width count
        (Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key RingProgram.flat
          (insertCode p t M cache k x entries))) (RingProgram.flat x))) := by
  sorry

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end
