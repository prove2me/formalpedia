-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_UniversalRowDataProgram_active_eval
-- name    : OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.active_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:41:17.392075+00:00
-- url     : https://prove2.me/theorems/bde25e75-5311-4dda-8123-68232ed51c3b
-- title:
--   OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.active_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.active_eval` of [lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowDataProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowDataProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram`, with `open BitProgram StructuredCalls StackRoutines`, `open UniversalRowGather (Data Word)`, `open UniversalRowLoop (Tables Valid ready)`, `open UniversalRowFactorLoop (indexWord)`):
--
--   ```lean
--   theorem active_eval (t : Tables) (width rowWidth : Word) (positions : List ℕ)
--       (valid : Valid t width rowWidth positions) (a : Data)
--       (ha : ready t width rowWidth positions a) (h17 : a.stacks 17 = [])
--       (h31 : a.stacks 31 = [false]) :
--       ∃ n ≤ activeCost t width rowWidth positions, ∃ b : Data, Eval active n a b ∧
--         b.stacks = Function.update a.stacks 31
--           (Encoding.encodeList UniversalRowProgram.encodeTerm
--             (positions.map (UniversalRowLoop.term t positions)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.Word` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowGather.Word`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.Tables` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.Term` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.term` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.Valid` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowGather.Data` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.ready` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.active` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.activeCost` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.encodeTerm` (definitions bundle `OAIQ081S180` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowDataProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.active_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S180

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.Subexp.UniversalRowDataProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)
open UniversalRowLoop (Tables Valid ready)
open UniversalRowFactorLoop (indexWord)

theorem active_eval (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (valid : Valid t width rowWidth positions) (a : Data)
    (ha : ready t width rowWidth positions a) (h17 : a.stacks 17 = [])
    (h31 : a.stacks 31 = [false]) :
    ∃ n ≤ activeCost t width rowWidth positions, ∃ b : Data, Eval active n a b ∧
      b.stacks = Function.update a.stacks 31
        (Encoding.encodeList UniversalRowProgram.encodeTerm
          (positions.map (UniversalRowLoop.term t positions))) := by
  sorry

end SubexponentialSAT.Subexp.UniversalRowDataProgram

end OAI.Algorithms
end
