-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram_Selector_familyInit_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.familyInit_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:45:59.561276+00:00
-- url     : https://prove2.me/theorems/2334fa34-76a2-401e-919f-be2f187e2a64
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.familyInit_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.familyInit_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparsePriorityProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparsePriorityProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector`, with `open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem familyInit_eval (F : Formula) (width : List Bool) (d : Data)
--       (h13 : d.stacks 13 = Filter.formulaCode F)
--       (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = [])
--       (h9 : d.stacks 9 = []) (h10 : d.stacks 10 = []) (h11 : d.stacks 11 = [])
--       (h12 : d.stacks 12 = []) (h16 : d.stacks 16 = []) (h18 : d.stacks 18 = []) :
--       ∃ t ≤ familyInitBound F width, ∃ e : Data,
--         Eval (familyInit width) t d e ∧
--         e.stacks = Function.update (Function.update d.stacks 16 width) 18
--           (Filter.formulaCode (widthFamily F width)) ∧
--         (∀ i : Fin 24, 16 ≤ i.val → e.regs i = d.regs i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Formula` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Filter.formulaCode` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.Data` (definitions bundle `OAIQ081S096` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.familyInitBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.widthFamily` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.familyInit` (definitions bundle `OAIQ081S136` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/SparsePriorityProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.familyInit_eval)

import Mathlib
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace Selector

theorem familyInit_eval (F : Formula) (width : List Bool) (d : Data)
    (h13 : d.stacks 13 = Filter.formulaCode F)
    (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = [])
    (h9 : d.stacks 9 = []) (h10 : d.stacks 10 = []) (h11 : d.stacks 11 = [])
    (h12 : d.stacks 12 = []) (h16 : d.stacks 16 = []) (h18 : d.stacks 18 = []) :
    ∃ t ≤ familyInitBound F width, ∃ e : Data,
      Eval (familyInit width) t d e ∧
      e.stacks = Function.update (Function.update d.stacks 16 width) 18
        (Filter.formulaCode (widthFamily F width)) ∧
      (∀ i : Fin 24, 16 ≤ i.val → e.regs i = d.regs i) := by
  sorry

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end
