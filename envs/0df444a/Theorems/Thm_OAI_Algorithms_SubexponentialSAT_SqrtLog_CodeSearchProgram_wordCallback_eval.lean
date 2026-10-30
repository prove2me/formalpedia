-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_wordCallback_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:06:52.867404+00:00
-- url     : https://prove2.me/theorems/55e6ad30-d28e-47c5-b964-a7cdb4b7dde3
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramCallback.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramCallback.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage`, `open StructuredProgram (Atom)`):
--
--   ```lean
--   theorem wordCallback_eval {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
--       (x : Fin D → SparseCode.F3) (d : ℕ) (a : SearchState) (he : WorkEmpty a)
--       (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
--       (hd : a.stacks 20 = List.replicate d true) (htmp : a.stacks 23 = [])
--       (hx : a.stacks 22 = (scalarFrames (List.ofFn x)).reverse) :
--       ∃ (n : ℕ) (out : SearchState), n ≤ callbackBudget t D d ∧
--         Eval wordCallback n a out ∧ WorkEmpty out ∧
--         out.regs 15 = decide (wordRejects Q x d) ∧
--         out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 ∧ out.stacks 22 = [] ∧
--         (∀ i : Fin 24, 18 ≤ i.val → i ≠ 22 → out.stacks i = a.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.F3` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordRejects` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.SearchState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.scalarFrames` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.WorkEmpty` (definitions bundle `OAIQ081S102` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchProgramCallback.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval)

import Mathlib
import Definitions.Def_OAIQ081S102

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

theorem wordCallback_eval {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) (a : SearchState) (he : WorkEmpty a)
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true) (htmp : a.stacks 23 = [])
    (hx : a.stacks 22 = (scalarFrames (List.ofFn x)).reverse) :
    ∃ (n : ℕ) (out : SearchState), n ≤ callbackBudget t D d ∧
      Eval wordCallback n a out ∧ WorkEmpty out ∧
      out.regs 15 = decide (wordRejects Q x d) ∧
      out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 ∧ out.stacks 22 = [] ∧
      (∀ i : Fin 24, 18 ≤ i.val → i ≠ 22 → out.stacks i = a.stacks i) := by
  sorry

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end
