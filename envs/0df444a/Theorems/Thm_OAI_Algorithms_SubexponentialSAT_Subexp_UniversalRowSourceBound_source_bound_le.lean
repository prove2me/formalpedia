-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_UniversalRowSourceBound_source_bound_le
-- name    : OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.source_bound_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:01:40.866139+00:00
-- url     : https://prove2.me/theorems/1bcf1f00-b80f-4ddc-9bbc-6b54ac1d225d
-- title:
--   OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.source_bound_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.source_bound_le` of [lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowSourceBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowSourceBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound`, with `open UniversalRowProgram`, `open UniversalRowFactorLoop (indexWord)`):
--
--   ```lean
--   theorem source_bound_le (t : UniversalRowLoop.Tables) (width rowWidth : Word)
--       (positions : List ℕ) (delta limit zero one : Word) (S : ℕ)
--       (valid : UniversalRowLoop.Valid t width rowWidth positions)
--       (hlen : positions.length ≤ S) (hpos : ∀ i ∈ positions, i ≤ S)
--       (hw : width.length ≤ S) (hr : rowWidth.length ≤ S)
--       (hd : delta.length ≤ S) (hl : limit.length ≤ S)
--       (hz : zero.length ≤ S) (ho : one.length ≤ S) :
--       UniversalRowSourceProgram.bound t width rowWidth positions delta limit zero one ≤ sourceBound S ∧
--         (rowCode zero one (zero ++ one) (UniversalRowDataProgram.row t positions delta limit)).length ≤
--           sourceLengthBound S
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.Tables` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.sourceLengthBound` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.Word` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.row` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.sourceBound` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.Valid` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.rowCode` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceProgram.bound` (definitions bundle `OAIQ081S186` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.nativeBudget_le` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.source_bounds` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/UniversalRowSourceBound.lean (declaration OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.source_bound_le)

import Mathlib
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.Subexp.UniversalRowSourceBound

open UniversalRowProgram
open UniversalRowFactorLoop (indexWord)

theorem source_bound_le (t : UniversalRowLoop.Tables) (width rowWidth : Word)
    (positions : List ℕ) (delta limit zero one : Word) (S : ℕ)
    (valid : UniversalRowLoop.Valid t width rowWidth positions)
    (hlen : positions.length ≤ S) (hpos : ∀ i ∈ positions, i ≤ S)
    (hw : width.length ≤ S) (hr : rowWidth.length ≤ S)
    (hd : delta.length ≤ S) (hl : limit.length ≤ S)
    (hz : zero.length ≤ S) (ho : one.length ≤ S) :
    UniversalRowSourceProgram.bound t width rowWidth positions delta limit zero one ≤ sourceBound S ∧
      (rowCode zero one (zero ++ one) (UniversalRowDataProgram.row t positions delta limit)).length ≤
        sourceLengthBound S := by
  sorry

end SubexponentialSAT.Subexp.UniversalRowSourceBound

end OAI.Algorithms
end
