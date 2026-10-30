-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBankFrame_lookup_lifted
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame.lookup_lifted
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:30:20.191982+00:00
-- url     : https://prove2.me/theorems/3d73d157-36fe-460f-8ec3-90016d239df7
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame.lookup_lifted: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame.lookup_lifted` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankFrameLookup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankFrameLookup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp`):
--
--   ```lean
--   theorem lookup_lifted {R S : ℕ} (register : Fin 6 → Fin R) (stack : Fin 16 → Fin S)
--       (hregister : Function.Injective register) (hstack : Function.Injective stack)
--       (a : State R S) (records : List (List Bool × List Bool)) (row col : List Bool)
--       (mr mc : GlobalBasisMetadata.Metadata)
--       (hr : records.lookup row=some mr.encode) (hc : records.lookup col=some mc.encode)
--       (ha : projectState register stack a=LookupPair.state (a.regs ∘ register)
--         (SelectorProgram.rawRecords records) row col [] [] [] [] [] []) :
--       ∃ n ≤ 400*(GlobalBasisMetadata.volume records row)^2+
--           400*(GlobalBasisMetadata.volume records col)^2+1,
--         ∃ e : State R S,
--         Eval (.call (ProgramLinking.liftProgram LookupPair.program register stack)) n a e ∧
--         projectState register stack e=
--           LookupPair.state ![false,false,false,false,mr.coveredFlag,mc.coveredFlag]
--             (SelectorProgram.rawRecords records) row col mr.block mr.typeCode mr.rank
--               mc.block mc.typeCode mc.rank ∧
--         (∀ j, (¬ ∃ i, stack i=j) → e.stacks j=a.stacks j) ∧
--         (∀ j, (¬ ∃ i, register i=j) → e.regs j=a.regs j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.ProgramLinking.liftProgram`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.Metadata` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.rawRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.Metadata.block`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.Metadata.encode`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.Metadata.rank` and `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.Metadata.typeCode` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.volume` (definitions bundle `OAIQ081S056` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.Metadata.coveredFlag` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.program` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.state` (definitions bundle `OAIQ081S123` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.command_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankFrameLookup.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame.lookup_lifted)

import Mathlib
import Definitions.Def_OAIQ081S064
import Definitions.Def_OAIQ081S123

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem lookup_lifted {R S : ℕ} (register : Fin 6 → Fin R) (stack : Fin 16 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (a : State R S) (records : List (List Bool × List Bool)) (row col : List Bool)
    (mr mc : GlobalBasisMetadata.Metadata)
    (hr : records.lookup row=some mr.encode) (hc : records.lookup col=some mc.encode)
    (ha : projectState register stack a=LookupPair.state (a.regs ∘ register)
      (SelectorProgram.rawRecords records) row col [] [] [] [] [] []) :
    ∃ n ≤ 400*(GlobalBasisMetadata.volume records row)^2+
        400*(GlobalBasisMetadata.volume records col)^2+1,
      ∃ e : State R S,
      Eval (.call (ProgramLinking.liftProgram LookupPair.program register stack)) n a e ∧
      projectState register stack e=
        LookupPair.state ![false,false,false,false,mr.coveredFlag,mc.coveredFlag]
          (SelectorProgram.rawRecords records) row col mr.block mr.typeCode mr.rank
            mc.block mc.typeCode mc.rank ∧
      (∀ j, (¬ ∃ i, stack i=j) → e.stacks j=a.stacks j) ∧
      (∀ j, (¬ ∃ i, register i=j) → e.regs j=a.regs j) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

end OAI.Algorithms
end
