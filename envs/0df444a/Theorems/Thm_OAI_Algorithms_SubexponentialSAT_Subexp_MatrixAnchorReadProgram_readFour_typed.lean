-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_MatrixAnchorReadProgram_readFour_typed
-- name    : OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readFour_typed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:55:31.46536+00:00
-- url     : https://prove2.me/theorems/74c5f237-b856-4659-ad90-1fc0e5efc7a3
-- title:
--   OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readFour_typed: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readFour_typed` of [lean/OAI/Algorithms/SubexponentialSAT/Subexp/MatrixAnchorTypes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/MatrixAnchorTypes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram`, with `open BitProgram StructuredCalls StackRoutines MulticolorTypes`):
--
--   ```lean
--   theorem readFour_typed (a : Data) (words : Fin 4 → Word r Q) (t : Fin Q)
--       (hwork : ∀ j : Fin 42, j.val < 9 → a.stacks j = [])
--       (hd : ∀ i, a.stacks (target i) = [])
--       (hs : ∀ i, a.stacks (source i) = ReadPlan.encodeWord (words i))
--       (hi : (a.stacks 37).length = t.val) (hw : (a.stacks 21).length = r) :
--       Eval readFour (4 * (9 * (Q * r) + t.val * (14 * r + 17) + 30 * r + 43)) a
--         (fourReadResult a (fun i => colorWord (words i t)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.source` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.target` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.colorWord` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan.encodeWord` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readFour` (definitions bundle `OAIQ081S056` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.Data` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.fourReadResult` (definitions bundle `OAIQ081S081` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/MatrixAnchorTypes.lean (declaration OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readFour_typed)

import Mathlib
import Definitions.Def_OAIQ081S081

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

open BitProgram StructuredCalls StackRoutines MulticolorTypes

variable {r Q Δ : ℕ}

theorem readFour_typed (a : Data) (words : Fin 4 → Word r Q) (t : Fin Q)
    (hwork : ∀ j : Fin 42, j.val < 9 → a.stacks j = [])
    (hd : ∀ i, a.stacks (target i) = [])
    (hs : ∀ i, a.stacks (source i) = ReadPlan.encodeWord (words i))
    (hi : (a.stacks 37).length = t.val) (hw : (a.stacks 21).length = r) :
    Eval readFour (4 * (9 * (Q * r) + t.val * (14 * r + 17) + 30 * r + 43)) a
      (fourReadResult a (fun i => colorWord (words i t))) := by
  sorry

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
end
