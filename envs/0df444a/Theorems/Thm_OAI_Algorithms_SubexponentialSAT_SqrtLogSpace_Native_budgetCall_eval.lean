-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_budgetCall_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.budgetCall_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:19:38.893057+00:00
-- url     : https://prove2.me/theorems/9a2772e3-fe06-4620-ad37-6174c9a96422
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.budgetCall_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.budgetCall_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeSetupSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeSetupSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native`, with `open BitProgram StructuredCalls BinaryArithmetic`):
--
--   ```lean
--   theorem budgetCall_eval (k : ℕ) (hk : 2 ≤ k) (s : List Bool) (a : State 80 1220)
--       (hports : ∀ j, a.stacks (budgetStacks j) = if j = 0 then s else []) :
--       ∃ steps b M B,
--         Eval (budgetCall k) steps a b ∧
--         steps ≤ DisjointReuse.SparseBudgetProgram.commandCost k s + 1 ∧
--         toNat M = DisjointReuse.SparseBudget.chooseM k 1 (toNat s) (by decide) ∧
--         toNat B = 4 * toNat M ^ (k - 1) ∧
--         (∀ j, b.stacks (budgetStacks j) = if j = 0 then s else if j = 1 then M
--           else if j = 2 then B else []) ∧
--         (∀ i, (¬ ∃ j, budgetStacks j = i) → b.stacks i = a.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.budgetStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram.commandCost` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.budgetCall` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeSetupSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.budgetCall_eval)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic

theorem budgetCall_eval (k : ℕ) (hk : 2 ≤ k) (s : List Bool) (a : State 80 1220)
    (hports : ∀ j, a.stacks (budgetStacks j) = if j = 0 then s else []) :
    ∃ steps b M B,
      Eval (budgetCall k) steps a b ∧
      steps ≤ DisjointReuse.SparseBudgetProgram.commandCost k s + 1 ∧
      toNat M = DisjointReuse.SparseBudget.chooseM k 1 (toNat s) (by decide) ∧
      toNat B = 4 * toNat M ^ (k - 1) ∧
      (∀ j, b.stacks (budgetStacks j) = if j = 0 then s else if j = 1 then M
        else if j = 2 then B else []) ∧
      (∀ i, (¬ ∃ j, budgetStacks j = i) → b.stacks i = a.stacks i) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end
