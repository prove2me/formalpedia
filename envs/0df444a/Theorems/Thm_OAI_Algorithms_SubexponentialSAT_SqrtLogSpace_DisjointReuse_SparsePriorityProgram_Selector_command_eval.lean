-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram_Selector_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.command_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:44:36.957184+00:00
-- url     : https://prove2.me/theorems/acca653e-9618-4fe7-a9d2-dcc90c117433
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparsePriorityProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparsePriorityProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector`, with `open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem command_eval (k : ℕ) (F : Formula) (base : List Bool) (d : Data)
--       (hd : Boundary F base d) (hwidth : ∀ C ∈ F, C.length ≤ k) :
--       ∃ t ≤ 1 + chainBudget F base (passes k), ∃ e : Data,
--         Eval (command k) t d e ∧
--         (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
--         (e.regs 23 = false → e.stacks = d.stacks ∧
--           ∀ c H, (c, H) ∈ rawCandidates k F → 0 < H.length → H.length < c →
--             (selectedRaw F c H).length < BinaryArithmetic.toNat base ^ (c - H.length)) ∧
--         (e.regs 23 = true → ∃ c H, RawPriority k F (BinaryArithmetic.toNat base) c H ∧
--           e.stacks 9 = Filter.clauseCode H ∧
--           e.stacks 12 = Filter.formulaCode (selectedRaw F c H))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Clause` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.passes` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Filter.clauseCode` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Formula` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.RawPriority`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.rawCandidates` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.selectedRaw` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Filter.formulaCode` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.Data` (definitions bundle `OAIQ081S096` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.chainBudget` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.Boundary` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.command` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.selectCurrent_execution` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparsePriorityProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.command_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace Selector

theorem command_eval (k : ℕ) (F : Formula) (base : List Bool) (d : Data)
    (hd : Boundary F base d) (hwidth : ∀ C ∈ F, C.length ≤ k) :
    ∃ t ≤ 1 + chainBudget F base (passes k), ∃ e : Data,
      Eval (command k) t d e ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      (e.regs 23 = false → e.stacks = d.stacks ∧
        ∀ c H, (c, H) ∈ rawCandidates k F → 0 < H.length → H.length < c →
          (selectedRaw F c H).length < BinaryArithmetic.toNat base ^ (c - H.length)) ∧
      (e.regs 23 = true → ∃ c H, RawPriority k F (BinaryArithmetic.toNat base) c H ∧
        e.stacks 9 = Filter.clauseCode H ∧
        e.stacks 12 = Filter.formulaCode (selectedRaw F c H)) := by
  sorry

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end
