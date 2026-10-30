-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgramScalar_scalarProgram_runsIn_total
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:53:57.003364+00:00
-- url     : https://prove2.me/theorems/3c5a3b2c-49ba-4db1-bf79-cdbc2fd908e5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarStep.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarStep.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.SqrtLog.RowSelectionProgram`):
--
--   ```lean
--   theorem scalarProgram_runsIn_total (xs : List Triple) (regs : Fin 8 → Bool)
--       (acc : WordPair) (A B : ℕ) (ha : pairLength acc ≤ A) (hx : Bounded B xs) :
--       ∃ r result,
--         RunsIn scalarProgram
--           (200000000*(xs.length+1)*(A+xs.length*termGrowth B+B+4)^2+1)
--           ((state regs acc ([],[]) ([],[]) (pairEncoding (tripleWords xs))).withPC
--             (some scalarProgram.entry))
--           ((state r result ([],[]) ([],[]) []).withPC none) ∧
--         pairValue result = pairValue acc+(xs.map termValue).sum ∧
--         wordTotal result = wordTotal acc+(xs.map termTotal).sum ∧
--         pairLength result ≤ A+xs.length*termGrowth B
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termGrowth` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairEncoding` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.Triple` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.tripleWords` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.state` (definitions bundle `OAIQ081S071` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarCommand` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram` (definitions bundle `OAIQ081S073` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.Bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termTotal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termValue` (definitions bundle `OAIQ081S075` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarStep.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total)

import Mathlib
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S075

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem scalarProgram_runsIn_total (xs : List Triple) (regs : Fin 8 → Bool)
    (acc : WordPair) (A B : ℕ) (ha : pairLength acc ≤ A) (hx : Bounded B xs) :
    ∃ r result,
      RunsIn scalarProgram
        (200000000*(xs.length+1)*(A+xs.length*termGrowth B+B+4)^2+1)
        ((state regs acc ([],[]) ([],[]) (pairEncoding (tripleWords xs))).withPC
          (some scalarProgram.entry))
        ((state r result ([],[]) ([],[]) []).withPC none) ∧
      pairValue result = pairValue acc+(xs.map termValue).sum ∧
      wordTotal result = wordTotal acc+(xs.map termTotal).sum ∧
      pairLength result ≤ A+xs.length*termGrowth B := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end
