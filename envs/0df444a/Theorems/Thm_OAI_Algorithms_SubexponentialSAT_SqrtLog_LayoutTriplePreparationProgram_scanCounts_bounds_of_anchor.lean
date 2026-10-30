-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram_scanCounts_bounds_of_anchor
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanCounts_bounds_of_anchor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:48:05.117802+00:00
-- url     : https://prove2.me/theorems/e0c3df50-38cf-4280-828e-8f7026187d5c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanCounts_bounds_of_anchor: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanCounts_bounds_of_anchor` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgramEntrySemantics.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgramEntrySemantics.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram`, with `open SubexponentialSAT.MulticolorTypes`, `open SubexponentialSAT.Subexp.MatrixScanProgram SubexponentialSAT.Subexp.MatrixEntryEvaluation`, `open SubexponentialSAT.Subexp.MatrixEntryKernel SubexponentialSAT.Subexp.MatrixExtendedEntryProgram`):
--
--   ```lean
--   theorem scanCounts_bounds_of_anchor (t : Fin Q) (u y : UniversalType r Q 1)
--       (ha : anchorValid (0 : Fin 1) t u y) (hc : AllCompatible (0 : Fin 1) u y) :
--       0 < unchangedCount (rows (0 : Fin 1) u y) ∧
--         unchangedCount (rows (0 : Fin 1) u y) ≤ Q ∧
--         transposedCount (rows (0 : Fin 1) u y) ≤ Q
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.anchorValid` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanProgram.transposedCount` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanProgram.unchangedCount` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryEvaluation.rows` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.AllCompatible` (definitions bundle `OAIQ081S064` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgramEntrySemantics.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanCounts_bounds_of_anchor)

import Mathlib
import Definitions.Def_OAIQ081S055
import Definitions.Def_OAIQ081S064

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixScanProgram SubexponentialSAT.Subexp.MatrixEntryEvaluation
open SubexponentialSAT.Subexp.MatrixEntryKernel SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

variable {r Q : ℕ}

theorem scanCounts_bounds_of_anchor (t : Fin Q) (u y : UniversalType r Q 1)
    (ha : anchorValid (0 : Fin 1) t u y) (hc : AllCompatible (0 : Fin 1) u y) :
    0 < unchangedCount (rows (0 : Fin 1) u y) ∧
      unchangedCount (rows (0 : Fin 1) u y) ≤ Q ∧
      transposedCount (rows (0 : Fin 1) u y) ≤ Q := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end
