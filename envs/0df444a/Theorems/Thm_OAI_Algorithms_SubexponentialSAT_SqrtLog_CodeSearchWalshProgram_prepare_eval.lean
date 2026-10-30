-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchWalshProgram_prepare_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.prepare_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:58:56.567741+00:00
-- url     : https://prove2.me/theorems/40c32a84-b1c1-48c5-85b0-8cb9543c3127
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.prepare_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.prepare_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchWalshProgramChecks.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchWalshProgramChecks.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem prepare_eval (d : Data) (hd : ∀ j : Fin 14, 3 ≤ j.val → d.stacks j = []) :
--       ∃ t ≤ 600 * (2 * size d + 4)^2 + 1, ∃ e : Data,
--         Eval prepare t d e ∧
--         BinaryArithmetic.toNat (e.stacks 3) = (d.stacks 2).length ∧
--         BinaryArithmetic.toNat (e.stacks 4) = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) ∧
--         BinaryArithmetic.toNat (e.stacks 5) = 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ∧
--         BinaryArithmetic.toNat (e.stacks 6) = BinaryArithmetic.toNat (d.stacks 1) + 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ∧
--         BinaryArithmetic.toNat (e.stacks 7) = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) + BinaryArithmetic.toNat (d.stacks 1) ∧
--         (∀ j : Fin 14, 3 ≤ j.val → j.val ≤ 7 → (e.stacks j).length ≤ 2 * size d + 4) ∧
--         (∀ j : Fin 14, (j.val < 3 ∨ 7 < j.val) → e.stacks j = d.stacks j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.prepare` (definitions bundle `OAIQ081S069` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.size` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CodeSearchWalshProgramChecks.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.prepare_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S084

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem prepare_eval (d : Data) (hd : ∀ j : Fin 14, 3 ≤ j.val → d.stacks j = []) :
    ∃ t ≤ 600 * (2 * size d + 4)^2 + 1, ∃ e : Data,
      Eval prepare t d e ∧
      BinaryArithmetic.toNat (e.stacks 3) = (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 4) = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) ∧
      BinaryArithmetic.toNat (e.stacks 5) = 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 6) = BinaryArithmetic.toNat (d.stacks 1) + 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 7) = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) + BinaryArithmetic.toNat (d.stacks 1) ∧
      (∀ j : Fin 14, 3 ≤ j.val → j.val ≤ 7 → (e.stacks j).length ≤ 2 * size d + 4) ∧
      (∀ j : Fin 14, (j.val < 3 ∨ 7 < j.val) → e.stacks j = d.stacks j) := by
  sorry

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end
