-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsReadoutProgram_fetchAdd_code
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_code
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:35:47.79716+00:00
-- url     : https://prove2.me/theorems/d2f22e5f-75ee-4027-86a0-bd46833a435c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_code: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_code` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsReadoutProgramFetch.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsReadoutProgramFetch.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram.Dictionary`):
--
--   ```lean
--   theorem fetchAdd_code (p e : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p e)
--       (cache : RingProgram.ScalarCache p e) {d : ℕ}
--       (key : K → List Bool) (hk : Function.Injective key)
--       (entries : List (K × RingProgram.Code (Word (baseWidth p e)) d)) (k : K)
--       (acc : RingProgram.Code (Word (baseWidth p e)) d)
--       (regs : Fin 8 → Bool) (width count : List Bool)
--       (hc : count.length = d) (hw : width.length = baseWidth p e) :
--       let encoded := Squarefree.Program.encodeDictionary key RingProgram.flat entries
--       ∃ n ≤ fetchBudget encoded (key k) (codeBranchBudget (baseWidth p e) d), ∃ rr,
--         Eval fetchAdd n (machine regs (inputTape M.bits width count encoded (key k) (RingProgram.flat acc)))
--           (machine rr (fetchedTape M.bits width count encoded (key k) (RingProgram.flat acc)
--             (RingProgram.flat (addFetched p e M cache entries k acc))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.codeBranchBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.encodeDictionary` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchedTape` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.inputTape` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.machine` (definitions bundle `OAIQ081S110` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.addFetched` (definitions bundle `OAIQ081S130` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.program_runsIn` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsReadoutProgramFetch.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_code)

import Mathlib
import Definitions.Def_OAIQ081S130

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

variable {K : Type*} [DecidableEq K]

theorem fetchAdd_code (p e : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p e)
    (cache : RingProgram.ScalarCache p e) {d : ℕ}
    (key : K → List Bool) (hk : Function.Injective key)
    (entries : List (K × RingProgram.Code (Word (baseWidth p e)) d)) (k : K)
    (acc : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p e) :
    let encoded := Squarefree.Program.encodeDictionary key RingProgram.flat entries
    ∃ n ≤ fetchBudget encoded (key k) (codeBranchBudget (baseWidth p e) d), ∃ rr,
      Eval fetchAdd n (machine regs (inputTape M.bits width count encoded (key k) (RingProgram.flat acc)))
        (machine rr (fetchedTape M.bits width count encoded (key k) (RingProgram.flat acc)
          (RingProgram.flat (addFetched p e M cache entries k acc)))) := by
  sorry

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end
