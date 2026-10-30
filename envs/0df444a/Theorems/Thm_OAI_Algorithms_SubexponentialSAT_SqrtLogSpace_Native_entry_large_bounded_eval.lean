-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_entry_large_bounded_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entry_large_bounded_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:19:35.235612+00:00
-- url     : https://prove2.me/theorems/4b61be87-0e49-4202-a806-02cc2f2c3a5e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entry_large_bounded_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entry_large_bounded_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeEntrySpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeEntrySpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native`, with `open BitProgram StructuredCalls DisjointReuse.DFSVisit`):
--
--   ```lean
--   theorem entry_large_bounded_eval {cutoff n frontSteps steps bound : ℕ}
--       (large : Cmd 80 1220) (F : SAT.CNF (Fin n)) (binary : List Bool)
--       (a b : State 80 1220) (hn : cutoff < n)
--       (hfront : Eval frontendCommand frontSteps
--         (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) a)
--       (hfrontTime : frontSteps ≤ frontendBound F)
--       (ready : FrontendReady F binary a) (hlen : binary.length ≤ n)
--       (hfrontBudget : Encoding.formulaBitLength F +
--         4000 * (Encoding.formulaBitLength F + 1) ^ 2 ≤ bound)
--       (hdispatchBudget : 1224 * (Encoding.formulaBitLength F + 1) + 10 * n + 28 ≤ bound)
--       (hlarge : BoundedEval large steps (FiniteFallback.cutoffResult a false) b bound) :
--       BoundedEval (entryCommand cutoff large) (frontSteps + (10 * n + 29 + steps))
--         (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b bound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI.countStack` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredProgram.ioState` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.frontendBound` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.cutoffResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.FrontendReady` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entryCommand` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.frontendCommand` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeCNF`, `OAI.Algorithms.SubexponentialSAT.Encoding.formulaBitLength` and `OAI.Algorithms.SubexponentialSAT.SAT.CNF` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeEntrySpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entry_large_bounded_eval)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse.DFSVisit

theorem entry_large_bounded_eval {cutoff n frontSteps steps bound : ℕ}
    (large : Cmd 80 1220) (F : SAT.CNF (Fin n)) (binary : List Bool)
    (a b : State 80 1220) (hn : cutoff < n)
    (hfront : Eval frontendCommand frontSteps
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) a)
    (hfrontTime : frontSteps ≤ frontendBound F)
    (ready : FrontendReady F binary a) (hlen : binary.length ≤ n)
    (hfrontBudget : Encoding.formulaBitLength F +
      4000 * (Encoding.formulaBitLength F + 1) ^ 2 ≤ bound)
    (hdispatchBudget : 1224 * (Encoding.formulaBitLength F + 1) + 10 * n + 28 ≤ bound)
    (hlarge : BoundedEval large steps (FiniteFallback.cutoffResult a false) b bound) :
    BoundedEval (entryCommand cutoff large) (frontSteps + (10 * n + 29 + steps))
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b bound := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end
