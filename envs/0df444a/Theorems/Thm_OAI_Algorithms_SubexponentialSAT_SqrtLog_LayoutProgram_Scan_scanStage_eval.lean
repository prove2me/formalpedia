-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_Scan_scanStage_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:52:40.946584+00:00
-- url     : https://prove2.me/theorems/758b875c-0522-469e-b026-e6af7a0050b4
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScan.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScan.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan`, with `open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines`, `open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.MatrixEntryProgram`):
--
--   ```lean
--   theorem scanStage_eval (i : Fin Δ) (u y : UniversalType r Q Δ)
--       (cache0 cache1 cache2 cache3 : List Bool) (regs : Fin 9 → Bool) :
--       ∃ n ≤ scanStageCost r Q Δ i.val, ∃ out,
--         Eval scanStage n (scanInput i u y cache0 cache1 cache2 cache3 regs)
--           (counted (scanInput i u y cache0 cache1 cache2 cache3 regs) out
--             (MatrixScanProgram.unchangedCount (MatrixEntryEvaluation.rows i u y))
--             (MatrixScanProgram.transposedCount (MatrixEntryEvaluation.rows i u y))) ∧
--         out 7 = (decide (MatrixEntryKernel.SpectatorsAgree i u y) &&
--           (MatrixEntryEvaluation.rows i u y).all MatrixScanProgram.compatible)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanProgram.ColorRow` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.SpectatorsAgree` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanProgram.transposedCount` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanProgram.unchangedCount` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryEvaluation.rows` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryProgram.scanStageCost` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanProgram.compatible` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryProgram.scanStage` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanInput` (definitions bundle `OAIQ081S073` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryProgram.counted` (definitions bundle `OAIQ081S081` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScan.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval)

import Mathlib
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S081

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.Scan

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.MatrixEntryProgram

variable {r Q Δ : ℕ}

theorem scanStage_eval (i : Fin Δ) (u y : UniversalType r Q Δ)
    (cache0 cache1 cache2 cache3 : List Bool) (regs : Fin 9 → Bool) :
    ∃ n ≤ scanStageCost r Q Δ i.val, ∃ out,
      Eval scanStage n (scanInput i u y cache0 cache1 cache2 cache3 regs)
        (counted (scanInput i u y cache0 cache1 cache2 cache3 regs) out
          (MatrixScanProgram.unchangedCount (MatrixEntryEvaluation.rows i u y))
          (MatrixScanProgram.transposedCount (MatrixEntryEvaluation.rows i u y))) ∧
      out 7 = (decide (MatrixEntryKernel.SpectatorsAgree i u y) &&
        (MatrixEntryEvaluation.rows i u y).all MatrixScanProgram.compatible) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.Scan

end OAI.Algorithms
end
