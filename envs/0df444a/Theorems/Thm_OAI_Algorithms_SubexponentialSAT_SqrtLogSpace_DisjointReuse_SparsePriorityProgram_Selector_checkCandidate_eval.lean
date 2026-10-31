-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram_Selector_checkCandidate_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.checkCandidate_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:44:28.458573+00:00
-- url     : https://prove2.me/theorems/a363ff2b-05f0-418e-bf78-f40d14872c3b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.checkCandidate_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.checkCandidate_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparsePriorityProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparsePriorityProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector`, with `open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem checkCandidate_eval (F : Formula) (H : Clause) (width : List Bool) (d : Data)
--       (h9 : d.stacks 9 = Filter.clauseCode H) (h16 : d.stacks 16 = width)
--       (h18 : d.stacks 18 = Filter.formulaCode F)
--       (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = [])
--       (h10 : d.stacks 10 = []) (h11 : d.stacks 11 = []) (h12 : d.stacks 12 = []) :
--       ∃ t ≤ checkCandidateBound F H width (d.stacks 17), ∃ e : Data,
--         Eval checkCandidate t d e ∧
--         e.stacks = Function.update d.stacks 12 (Filter.formulaCode (selectedFamily F H width)) ∧
--         e.regs 4 = decide (BinaryArithmetic.toNat (d.stacks 17) ≤ (Filter.result F H width).length) ∧
--         (∀ i : Fin 24, 16 ≤ i.val → e.regs i = d.regs i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Clause` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Filter.clauseCode` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Formula` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Filter.formulaCode` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Filter.result` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.Data` (definitions bundle `OAIQ081S096` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.checkCandidateBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.selectedFamily` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.checkCandidate` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparsePriorityProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.checkCandidate_eval)

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

theorem checkCandidate_eval (F : Formula) (H : Clause) (width : List Bool) (d : Data)
    (h9 : d.stacks 9 = Filter.clauseCode H) (h16 : d.stacks 16 = width)
    (h18 : d.stacks 18 = Filter.formulaCode F)
    (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = [])
    (h10 : d.stacks 10 = []) (h11 : d.stacks 11 = []) (h12 : d.stacks 12 = []) :
    ∃ t ≤ checkCandidateBound F H width (d.stacks 17), ∃ e : Data,
      Eval checkCandidate t d e ∧
      e.stacks = Function.update d.stacks 12 (Filter.formulaCode (selectedFamily F H width)) ∧
      e.regs 4 = decide (BinaryArithmetic.toNat (d.stacks 17) ≤ (Filter.result F H width).length) ∧
      (∀ i : Fin 24, 16 ≤ i.val → e.regs i = d.regs i) := by
  sorry

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end
