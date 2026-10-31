-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_emit_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:43:02.26048+00:00
-- url     : https://prove2.me/theorems/ce8a055a-09fb-4a19-acbd-e39fce2adeb6
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes`):
--
--   ```lean
--   theorem emit_eval (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool)
--       (positions : List ℕ) (valid : UniversalRowLoop.Valid tables width rowWidth positions)
--       (delta limit zero one : List Bool) (a : Data)
--       (ha : UniversalRowLoop.ready tables width rowWidth positions
--         (projectState emitterRegs emitterPorts a))
--       (hd : a.stacks 274=delta) (hl : a.stacks 269=limit)
--       (hz : a.stacks 259=zero) (ho : a.stacks 266=one)
--       (h14 : a.stacks 270=[]) (h17 : a.stacks 273=[]) (h31 : a.stacks 287=[]) :
--       ∃ n ≤ UniversalRowSourceProgram.bound tables width rowWidth positions delta limit zero one,
--         ∃ b : Data, Eval emit n a b ∧
--           b.stacks=Function.update (Function.update a.stacks 274 []) 287
--             (UniversalRowProgram.rowCode zero one (zero++one)
--               (UniversalRowDataProgram.row tables positions delta limit))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.Tables`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emitterPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emitterRegs` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.row` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.Valid` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.ready` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Data` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.rowCode` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceProgram.bound` (definitions bundle `OAIQ081S186` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finish_universal_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit_eval)

import Mathlib
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem emit_eval (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool)
    (positions : List ℕ) (valid : UniversalRowLoop.Valid tables width rowWidth positions)
    (delta limit zero one : List Bool) (a : Data)
    (ha : UniversalRowLoop.ready tables width rowWidth positions
      (projectState emitterRegs emitterPorts a))
    (hd : a.stacks 274=delta) (hl : a.stacks 269=limit)
    (hz : a.stacks 259=zero) (ho : a.stacks 266=one)
    (h14 : a.stacks 270=[]) (h17 : a.stacks 273=[]) (h31 : a.stacks 287=[]) :
    ∃ n ≤ UniversalRowSourceProgram.bound tables width rowWidth positions delta limit zero one,
      ∃ b : Data, Eval emit n a b ∧
        b.stacks=Function.update (Function.update a.stacks 274 []) 287
          (UniversalRowProgram.rowCode zero one (zero++one)
            (UniversalRowDataProgram.row tables positions delta limit)) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end
