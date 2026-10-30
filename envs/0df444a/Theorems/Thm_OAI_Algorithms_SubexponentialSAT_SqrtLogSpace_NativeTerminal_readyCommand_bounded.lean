-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeTerminal_readyCommand_bounded
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand_bounded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:21:19.349102+00:00
-- url     : https://prove2.me/theorems/00a40d34-eea2-4065-a816-931b2383e28b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand_bounded: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand_bounded` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeTerminal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeTerminal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal`, with `open BitProgram StructuredCalls`, `open scoped BigOperators`, `open DisjointReuse.DFSVisit`):
--
--   ```lean
--   theorem readyCommand_bounded (a : Data) (n bound : ℕ) (records : List (List Bool))
--       (hbody : a.stacks 265 = Encoding.encodeList id records)
--       (hlow : ∀ i : Fin 1220, i.val < 9 → a.stacks i = [])
--       (hn : a.stacks 258 = Encoding.encodeNat n)
--       (hframe : ∀ i, (a.stacks i).length ≤ bound)
--       (hclassifier : 101 * (a.stacks 265).length + 103 ≤ bound)
--       (hpower : 5 * n + 6 ≤ bound) :
--       ∃ steps, steps ≤ 6 * bound + 100 * ((a.stacks 265).length + 1) + 11 * n + 31 ∧
--         BoundedEval readyCommand steps a (readyResult a n records) bound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyResult` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch.command_execution` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeTerminal.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand_bounded)

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

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

open BitProgram StructuredCalls
open scoped BigOperators

open DisjointReuse.DFSVisit

theorem readyCommand_bounded (a : Data) (n bound : ℕ) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records)
    (hlow : ∀ i : Fin 1220, i.val < 9 → a.stacks i = [])
    (hn : a.stacks 258 = Encoding.encodeNat n)
    (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hclassifier : 101 * (a.stacks 265).length + 103 ≤ bound)
    (hpower : 5 * n + 6 ≤ bound) :
    ∃ steps, steps ≤ 6 * bound + 100 * ((a.stacks 265).length + 1) + 11 * n + 31 ∧
      BoundedEval readyCommand steps a (readyResult a n records) bound := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal
end
