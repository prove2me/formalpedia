-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_UniversalRowMismatchTypes_filter_eval
-- name    : OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:22:27.382599+00:00
-- url     : https://prove2.me/theorems/8c34b16e-6422-4e8f-96fc-12ffba23341a
-- title:
--   OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter_eval` of [lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowMismatchTypes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowMismatchTypes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes`, with `open BitProgram StructuredCalls StackRoutines MulticolorTypes`):
--
--   ```lean
--   theorem filter_eval (left right : MulticolorTypes.Word r Q) (a : Data)
--       (hl : a.stacks 19 = ReadPlan.encodeWord left)
--       (hr : a.stacks 18 = ReadPlan.encodeWord right)
--       (hw : a.stacks 21 = List.replicate r true)
--       (hq : a.stacks 22 = List.replicate Q true)
--       (he : ∀ j : Fin 49, j ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 45] → a.stacks j = []) :
--       ∃ n ≤ UniversalRowMismatchProgram.budget Q r, ∃ b : Data,
--         Eval filter n a b ∧ b.stacks = Function.update a.stacks 45
--           (ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords
--             (MismatchPlanProgram.selectedPositions left right).reverse))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ProgramEncoding.encodeRecords` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan.encodeWord` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.indexRecords` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchProgram.budget` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.selectedPositions` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.Data` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter` (definitions bundle `OAIQ081S107` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_mismatch_branch` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowMismatchTypes.lean (declaration OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes.filter_eval)

import Mathlib
import Definitions.Def_OAIQ081S064
import Definitions.Def_OAIQ081S107

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.Subexp.UniversalRowMismatchTypes

open BitProgram StructuredCalls StackRoutines MulticolorTypes

variable {r Q Δ : ℕ}

theorem filter_eval (left right : MulticolorTypes.Word r Q) (a : Data)
    (hl : a.stacks 19 = ReadPlan.encodeWord left)
    (hr : a.stacks 18 = ReadPlan.encodeWord right)
    (hw : a.stacks 21 = List.replicate r true)
    (hq : a.stacks 22 = List.replicate Q true)
    (he : ∀ j : Fin 49, j ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 45] → a.stacks j = []) :
    ∃ n ≤ UniversalRowMismatchProgram.budget Q r, ∃ b : Data,
      Eval filter n a b ∧ b.stacks = Function.update a.stacks 45
        (ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords
          (MismatchPlanProgram.selectedPositions left right).reverse)) := by
  sorry

end SubexponentialSAT.Subexp.UniversalRowMismatchTypes

end OAI.Algorithms
end
