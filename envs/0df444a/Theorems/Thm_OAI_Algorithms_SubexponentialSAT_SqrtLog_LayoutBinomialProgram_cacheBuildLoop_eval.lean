-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutBinomialProgram_cacheBuildLoop_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.cacheBuildLoop_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:42:05.085006+00:00
-- url     : https://prove2.me/theorems/1fa4d3d0-7d5d-4b0a-af4c-3b39b72faa8c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.cacheBuildLoop_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.cacheBuildLoop_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutBinomialProgramCell.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutBinomialProgramCell.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.SqrtLog.RowSelectionProgram`, `open SubexponentialSAT.SqrtLog.LayoutProgramScalar`):
--
--   ```lean
--   theorem cacheBuildLoop_eval (regs : Fin 8 → Bool) (a : List Bool)
--       (xs : List (List Bool)) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
--       ∃ t ≤ 400*(a.length+1)*(xs.length+1)*(B+a.length+4)+2,
--       ∃ regs', Eval cacheBuildLoop t
--         (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
--         (buildState regs' [] [] (pairEncoding ((iterate a.length xs).map fun x => (x,[]))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.iterate` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairEncoding` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.buildState` (definitions bundle `OAIQ081S142` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.cacheBuildLoop` (definitions bundle `OAIQ081S166` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.binomial_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutBinomialProgramCell.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.cacheBuildLoop_eval)

import Mathlib
import Definitions.Def_OAIQ081S166

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

theorem cacheBuildLoop_eval (regs : Fin 8 → Bool) (a : List Bool)
    (xs : List (List Bool)) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 400*(a.length+1)*(xs.length+1)*(B+a.length+4)+2,
    ∃ regs', Eval cacheBuildLoop t
      (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
      (buildState regs' [] [] (pairEncoding ((iterate a.length xs).map fun x => (x,[])))) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end
