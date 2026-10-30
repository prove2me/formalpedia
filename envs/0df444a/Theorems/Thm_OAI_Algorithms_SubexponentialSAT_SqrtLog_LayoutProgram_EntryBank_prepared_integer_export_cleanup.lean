-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBank_prepared_integer_export_cleanup
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepared_integer_export_cleanup
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:05:19.376343+00:00
-- url     : https://prove2.me/theorems/a1244842-4f97-4049-b08b-b533fbed5175
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepared_integer_export_cleanup: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepared_integer_export_cleanup` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankFramePrepare.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankFramePrepare.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes`):
--
--   ```lean
--   theorem prepared_integer_export_cleanup (a : Data) (ht : a.stacks 199=[])
--       (h254 : a.stacks 254=[]) (h255 : a.stacks 255=[]) {n : ℕ} {b : IntegerEntry.Data}
--       (he : Eval IntegerEntry.command n
--         (projectState integerRegs integerPorts (Staging.result 0 1 prepareOps a)) b) :
--       let p := Staging.result 0 1 prepareOps a
--       let q := embedState integerRegs integerPorts p b
--       let e := Staging.result 0 1 exportOps q
--       let z := Staging.result 0 1 cleanupOps e
--       Eval (.seq prepare (.seq integer (.seq exportPair cleanup)))
--         (Staging.cost 0 1 prepareOps a+
--           ((n+1)+(Staging.cost 0 1 exportOps q+Staging.cost 0 1 cleanupOps e))) a z ∧
--       (∀ j : Fin 256, z.stacks j=
--         if j.val < 200 then [] else if j=255 then b.stacks 54
--           else if j=254 then b.stacks 53 else a.stacks j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.cleanupOps`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.exportOps`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.integerPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.integerRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepareOps` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` and `OAI.Algorithms.SubexponentialSAT.StructuredCalls.embedState` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Staging.cost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Staging.result` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.cleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.exportPair` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepare` (definitions bundle `OAIQ081S123` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.Data` (definitions bundle `OAIQ081S142` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.Data` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.integer` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.command` (definitions bundle `OAIQ081S174` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.inner_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankFramePrepare.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepared_integer_export_cleanup)

import Mathlib
import Definitions.Def_OAIQ081S174

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem prepared_integer_export_cleanup (a : Data) (ht : a.stacks 199=[])
    (h254 : a.stacks 254=[]) (h255 : a.stacks 255=[]) {n : ℕ} {b : IntegerEntry.Data}
    (he : Eval IntegerEntry.command n
      (projectState integerRegs integerPorts (Staging.result 0 1 prepareOps a)) b) :
    let p := Staging.result 0 1 prepareOps a
    let q := embedState integerRegs integerPorts p b
    let e := Staging.result 0 1 exportOps q
    let z := Staging.result 0 1 cleanupOps e
    Eval (.seq prepare (.seq integer (.seq exportPair cleanup)))
      (Staging.cost 0 1 prepareOps a+
        ((n+1)+(Staging.cost 0 1 exportOps q+Staging.cost 0 1 cleanupOps e))) a z ∧
    (∀ j : Fin 256, z.stacks j=
      if j.val < 200 then [] else if j=255 then b.stacks 54
        else if j=254 then b.stacks 53 else a.stacks j) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end
