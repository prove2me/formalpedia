-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram_factoredTotalEncodes_sum
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredTotalEncodes_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:54:11.659415+00:00
-- url     : https://prove2.me/theorems/0e53d76c-e931-4963-b1c5-e025b1556122
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredTotalEncodes_sum: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredTotalEncodes_sum` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgramInterface.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgramInterface.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram`, with `open scoped BigOperators`, `open RowSelectionProgram LayoutProgramScalar LayoutCoefficientRecurrence`):
--
--   ```lean
--   theorem factoredTotalEncodes_sum (A R d h : ℕ) (xs : List LayoutProgramScalar.Triple)
--       (he : FactoredTotalEncodes A R d h xs) :
--       (xs.map termTotal).sum = LayoutProgram.scalarMass R d h
--         (fun j => (LayoutCoefficientAlgorithm.coefficientAt A R j).natAbs)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.coefficientAt` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.scalarMass` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.Triple` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termTotal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.FactoredTotalEncodes` (definitions bundle `OAIQ081S075` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgramInterface.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredTotalEncodes_sum)

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
open RowSelectionProgram LayoutProgramScalar LayoutCoefficientRecurrence

theorem factoredTotalEncodes_sum (A R d h : ℕ) (xs : List LayoutProgramScalar.Triple)
    (he : FactoredTotalEncodes A R d h xs) :
    (xs.map termTotal).sum = LayoutProgram.scalarMass R d h
      (fun j => (LayoutCoefficientAlgorithm.coefficientAt A R j).natAbs) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end
