-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_finish_universal_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finish_universal_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:42:36.444043+00:00
-- url     : https://prove2.me/theorems/08a7df4c-9825-445a-974a-2d28562850df
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finish_universal_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finish_universal_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrameFinish.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrameFinish.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp`):
--
--   ```lean
--   theorem finish_universal_eval (a : Data) (ht : a.stacks 319=[]) (hclean : EmitterClean a)
--       (h274 : a.stacks 274=[]) (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[])
--       (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[])
--       (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool) (positions : List ℕ)
--       (valid : UniversalRowLoop.Valid tables width rowWidth positions)
--       (hv : a.stacks 67=tables.values.flatten) (hi : a.stacks 308=tables.inverses.flatten)
--       (hn : a.stacks 309=tables.negatives.flatten) (hr : a.stacks 310=tables.rows.flatten)
--       (hp : a.stacks 71=UniversalRowTermProgram.indices positions)
--       (hw : a.stacks 311=width) (hrw : a.stacks 312=rowWidth)
--       (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
--       ∃ n ≤ finishBound tables width rowWidth positions a B,
--         ∃ b : Data, Eval (.seq (.seq compareTypes (.seq delta (.seq stageEmitter emit))) cleanup) n a b ∧
--           b.stacks=Function.update (clearedStacks a) 287 (sourceWord tables positions a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.Tables` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowTermProgram.indices` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.Valid` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.Tables.rows` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.cleanup` (definitions bundle `OAIQ081S124` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.stageEmitter` (definitions bundle `OAIQ081S143` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareTypes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.delta` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Data` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.EmitterClean` (definitions bundle `OAIQ081S167` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.clearedStacks` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finishBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.sourceWord` (definitions bundle `OAIQ081S186` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_universal_cleanup_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBankFrameFinish.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.finish_universal_eval)

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
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem finish_universal_eval (a : Data) (ht : a.stacks 319=[]) (hclean : EmitterClean a)
    (h274 : a.stacks 274=[]) (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[])
    (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[])
    (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool) (positions : List ℕ)
    (valid : UniversalRowLoop.Valid tables width rowWidth positions)
    (hv : a.stacks 67=tables.values.flatten) (hi : a.stacks 308=tables.inverses.flatten)
    (hn : a.stacks 309=tables.negatives.flatten) (hr : a.stacks 310=tables.rows.flatten)
    (hp : a.stacks 71=UniversalRowTermProgram.indices positions)
    (hw : a.stacks 311=width) (hrw : a.stacks 312=rowWidth)
    (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∃ n ≤ finishBound tables width rowWidth positions a B,
      ∃ b : Data, Eval (.seq (.seq compareTypes (.seq delta (.seq stageEmitter emit))) cleanup) n a b ∧
        b.stacks=Function.update (clearedStacks a) 287 (sourceWord tables positions a) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end
