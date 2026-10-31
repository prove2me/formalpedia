-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceTyped_source_bounds
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.source_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:46:19.199628+00:00
-- url     : https://prove2.me/theorems/e01ee4dd-2987-4837-8547-f123a91e1235
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.source_bounds: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.source_bounds` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped`, with `open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.UniversalRowTableSource`):
--
--   ```lean
--   theorem source_bounds (encode : C → List Bool) (values inverse negative : Fin Q → C)
--       (difference : Fin Q → Fin Q → C) (width rowWidth : List Bool)
--       (hwidth : ∀ c,(encode c).length=width.length)
--       (hrow : rowWidth.length=Q*width.length) (s : Finset (Fin Q))
--       (delta limit zero one : List Bool) (S : ℕ)
--       (hQ : Q ≤ S) (hw : width.length ≤ S) (hr : rowWidth.length ≤ S)
--       (hd : delta.length ≤ S) (hl : limit.length ≤ S)
--       (hz : zero.length ≤ S) (ho : one.length ≤ S) :
--       UniversalRowSourceProgram.bound (tables encode values inverse negative difference)
--         width rowWidth (positions s) delta limit zero one ≤ UniversalRowSourceBound.sourceBound S ∧
--       (UniversalRowProgram.rowCode zero one (zero++one)
--         (UniversalRowDataProgram.row (tables encode values inverse negative difference)
--           (positions s) delta limit)).length ≤ UniversalRowSourceBound.sourceLengthBound S
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.sourceLengthBound` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.row`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.sourceBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.tables` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowTableSource.positions` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.rowCode` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceProgram.bound` (definitions bundle `OAIQ081S186` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.universal` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.source_bounds)

import Mathlib
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.UniversalRowTableSource

variable {C : Type*} {Q : ℕ}

theorem source_bounds (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (width rowWidth : List Bool)
    (hwidth : ∀ c,(encode c).length=width.length)
    (hrow : rowWidth.length=Q*width.length) (s : Finset (Fin Q))
    (delta limit zero one : List Bool) (S : ℕ)
    (hQ : Q ≤ S) (hw : width.length ≤ S) (hr : rowWidth.length ≤ S)
    (hd : delta.length ≤ S) (hl : limit.length ≤ S)
    (hz : zero.length ≤ S) (ho : one.length ≤ S) :
    UniversalRowSourceProgram.bound (tables encode values inverse negative difference)
      width rowWidth (positions s) delta limit zero one ≤ UniversalRowSourceBound.sourceBound S ∧
    (UniversalRowProgram.rowCode zero one (zero++one)
      (UniversalRowDataProgram.row (tables encode values inverse negative difference)
        (positions s) delta limit)).length ≤ UniversalRowSourceBound.sourceLengthBound S := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
end
