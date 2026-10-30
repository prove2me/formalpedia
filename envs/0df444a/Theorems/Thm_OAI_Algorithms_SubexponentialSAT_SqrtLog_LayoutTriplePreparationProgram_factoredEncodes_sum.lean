-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram_factoredEncodes_sum
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredEncodes_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:54:07.444948+00:00
-- url     : https://prove2.me/theorems/e835e593-f14f-4741-a8ee-109103c47e87
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredEncodes_sum: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredEncodes_sum` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgramInterface.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgramInterface.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram`, with `open scoped BigOperators`, `open SubexponentialSAT.SqrtLog.RowSelectionProgram`, `open SubexponentialSAT.SqrtLog.LayoutProgramScalar`, `open SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm`, `open SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence`):
--
--   ```lean
--   theorem factoredEncodes_sum (A R d h : ℕ) (xs : List Triple)
--       (he : FactoredEncodes A R d h xs) :
--       (xs.map termValue).sum = scalarSum A R d h
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarSum` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.Triple` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Triple` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termValue` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.FactoredEncodes` (definitions bundle `OAIQ081S075` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgramInterface.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredEncodes_sum)

import Mathlib
import Definitions.Def_OAIQ081S075

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open scoped BigOperators
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm
open SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

theorem factoredEncodes_sum (A R d h : ℕ) (xs : List Triple)
    (he : FactoredEncodes A R d h xs) :
    (xs.map termValue).sum = scalarSum A R d h := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end
