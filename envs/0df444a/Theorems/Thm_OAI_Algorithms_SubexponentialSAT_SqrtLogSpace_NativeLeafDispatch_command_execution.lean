-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafDispatch_command_execution
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch.command_execution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:20:24.939071+00:00
-- url     : https://prove2.me/theorems/a06f990a-99c0-4ef6-8afb-53cc683329f3
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch.command_execution: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch.command_execution` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafDispatch.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafDispatch.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch`, with `open BitProgram StructuredCalls DisjointReuse DFSVisit`):
--
--   ```lean
--   theorem command_execution (nonterminal : Cmd 80 1220) (leafTime bound : ℕ)
--       (hr : LeafReady k threshold parameterBound F a)
--       (hframe : ∀ i, (a.stacks i).length ≤ bound)
--       (hclassifier : 101 * (a.stacks 265).length + 103 ≤ bound)
--       (hpower : 5 * n + 6 ≤ bound)
--       (hcallback : [] ∉ F → F ≠ [] →
--         LeafReady k threshold parameterBound F
--           (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) →
--         (∀ i, ((NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)).stacks i).length
--           ≤ bound) →
--         ∃ t ≤ leafTime, ∃ e,
--           BoundedEval nonterminal t
--             (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) e bound ∧
--           LeafDone F (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) e) :
--       ∃ t ≤ 6 * bound + 100 * ((a.stacks 265).length + 1) + 11 * n + leafTime + 33,
--         ∃ e, BoundedEval (command nonterminal) t a e bound ∧ LeafDone F a e
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.clauseRecords` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.LeafDone`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.LeafReady` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch.command` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafDispatch.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch.command_execution)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch

open BitProgram StructuredCalls DisjointReuse DFSVisit

variable {n k parameterBound : ℕ} {threshold : List Bool}
  {F : RawCNF n} {a : Data}

theorem command_execution (nonterminal : Cmd 80 1220) (leafTime bound : ℕ)
    (hr : LeafReady k threshold parameterBound F a)
    (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hclassifier : 101 * (a.stacks 265).length + 103 ≤ bound)
    (hpower : 5 * n + 6 ≤ bound)
    (hcallback : [] ∉ F → F ≠ [] →
      LeafReady k threshold parameterBound F
        (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) →
      (∀ i, ((NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)).stacks i).length
        ≤ bound) →
      ∃ t ≤ leafTime, ∃ e,
        BoundedEval nonterminal t
          (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) e bound ∧
        LeafDone F (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) e) :
    ∃ t ≤ 6 * bound + 100 * ((a.stacks 265).length + 1) + 11 * n + leafTime + 33,
      ∃ e, BoundedEval (command nonterminal) t a e bound ∧ LeafDone F a e := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch
end
