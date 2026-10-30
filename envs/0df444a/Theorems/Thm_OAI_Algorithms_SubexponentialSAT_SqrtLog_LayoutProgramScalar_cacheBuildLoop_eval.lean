-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgramScalar_cacheBuildLoop_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:58:07.739091+00:00
-- url     : https://prove2.me/theorems/6ad936ee-d4fe-4fab-91d7-fd0d2ed6bbb2
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarCacheCell.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarCacheCell.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.SqrtLog.RowSelectionProgram`):
--
--   ```lean
--   theorem cacheBuildLoop_eval (regs : Fin 8 → Bool) (a : List Bool)
--       (xs : List (List Bool)) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
--       ∃ t ≤ 400*(a.length+1)*(xs.length+1)*(B+2*a.length*xs.length+4)+2,
--       ∃ regs', Eval cacheBuildLoop t
--         (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
--         (buildState regs' [] [] (pairEncoding ((cacheIter a.length xs).map fun x => (x,[]))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairEncoding` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheIter` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.buildState` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop` (definitions bundle `OAIQ081S143` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program_runsIn` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarCacheCell.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop_eval)

import Mathlib
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S143

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

theorem cacheBuildLoop_eval (regs : Fin 8 → Bool) (a : List Bool)
    (xs : List (List Bool)) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 400*(a.length+1)*(xs.length+1)*(B+2*a.length*xs.length+4)+2,
    ∃ regs', Eval cacheBuildLoop t
      (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
      (buildState regs' [] [] (pairEncoding ((cacheIter a.length xs).map fun x => (x,[])))) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end
