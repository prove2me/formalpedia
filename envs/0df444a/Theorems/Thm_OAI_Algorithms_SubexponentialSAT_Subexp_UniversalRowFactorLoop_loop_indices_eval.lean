-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_UniversalRowFactorLoop_loop_indices_eval
-- name    : OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.loop_indices_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:22:51.9085+00:00
-- url     : https://prove2.me/theorems/7c2f5044-4176-46b8-b56b-720a7746faa8
-- title:
--   OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.loop_indices_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.loop_indices_eval` of [lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowFactorLoop.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowFactorLoop.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop`, with `open BitProgram StructuredCalls StackRoutines`, `open UniversalRowGather (Data Word)`):
--
--   ```lean
--   theorem loop_indices_eval (differences negatives : List Word) (width : Word) (i : ℕ)
--       (positions : List ℕ) (suffix : Word) (base : Data)
--       (hbase : Ready differences negatives width (indexWord i) base)
--       (hacc : base.stacks 21 = [false])
--       (hds : ∀ row ∈ differences, row.length = width.length)
--       (hns : ∀ row ∈ negatives, row.length = width.length)
--       (hpositions : ∀ j ∈ positions, j < differences.length ∧ j < negatives.length)
--       (v pr f : Bool) :
--       ∃ n ≤ 3 + RecordPrograms.budget (callbackCost width.length i)
--           (positions.reverse.map indexWord), ∃ next : Data,
--         Eval loop n
--           (RecordPrograms.state ports base v pr f
--             (Encoding.encodeList id (positions.reverse.map indexWord) ++ suffix) [])
--           (RecordPrograms.state ports next false true false suffix []) ∧
--         Ready differences negatives width (indexWord i) next ∧
--         next.stacks 21 = Encoding.encodeList UniversalRowProgram.encodeFactor
--           (factors differences negatives i positions) ∧
--         (∀ j, j ≠ 21 → next.stacks j = base.stacks j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.budget` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.Word` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.callbackCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.factors`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.indexWord`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowGather.Word` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.Factor` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.state` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.ports` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowGather.Data` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.Ready` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.loop` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.encodeFactor` (definitions bundle `OAIQ081S173` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.active_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowFactorLoop.lean (declaration OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.loop_indices_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S173

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.Subexp.UniversalRowFactorLoop

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)

theorem loop_indices_eval (differences negatives : List Word) (width : Word) (i : ℕ)
    (positions : List ℕ) (suffix : Word) (base : Data)
    (hbase : Ready differences negatives width (indexWord i) base)
    (hacc : base.stacks 21 = [false])
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length)
    (hpositions : ∀ j ∈ positions, j < differences.length ∧ j < negatives.length)
    (v pr f : Bool) :
    ∃ n ≤ 3 + RecordPrograms.budget (callbackCost width.length i)
        (positions.reverse.map indexWord), ∃ next : Data,
      Eval loop n
        (RecordPrograms.state ports base v pr f
          (Encoding.encodeList id (positions.reverse.map indexWord) ++ suffix) [])
        (RecordPrograms.state ports next false true false suffix []) ∧
      Ready differences negatives width (indexWord i) next ∧
      next.stacks 21 = Encoding.encodeList UniversalRowProgram.encodeFactor
        (factors differences negatives i positions) ∧
      (∀ j, j ≠ 21 → next.stacks j = base.stacks j) := by
  sorry

end SubexponentialSAT.Subexp.UniversalRowFactorLoop

end OAI.Algorithms
end
