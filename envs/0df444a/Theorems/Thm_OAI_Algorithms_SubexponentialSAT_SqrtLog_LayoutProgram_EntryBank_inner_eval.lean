-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBank_inner_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.inner_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:05:22.604076+00:00
-- url     : https://prove2.me/theorems/e1442b19-7425-4514-9e53-7cfcc70b3738
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.inner_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.inner_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankInner.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankInner.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes`, `open RowSelectionProgram`):
--
--   ```lean
--   theorem inner_eval (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
--       (aWord : List Bool) (R : ℕ) (t : Fin Q) (u y : UniversalType r Q 1)
--       (a : Data) (S : ℕ)
--       (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
--       (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
--       (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
--       (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
--       (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
--       (hc : Cached a (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t u y)
--       (hsize : ∀ j : Fin 256, j.val < 212 → (a.stacks j).length ≤ S) :
--       let L := IntegerEntry.lengthBound R width.length (pairLength power) u y+power.1.length+1
--       ∃ n ≤ IntegerEntry.budget aWord.length R width.length (pairLength power) power.1.length t u y+
--           484*S+407*L+1073,
--         ∃ rf result, Eval inner n a (finish a rf result) ∧
--           pairValue result=IntegerEntry.value aWord.length R t u y ∧
--           LayoutProgramScalar.wordTotal result ≤ constraintMassBound Q R ∧ pairLength result ≤ L
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.H` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.constraintMassBound` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.lengthBound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.value` (definitions bundle `OAIQ081S073` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.Data` (definitions bundle `OAIQ081S142` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.Cached` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.finish` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.unsignedSaved` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.inner` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramEntryBankInner.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.inner_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open RowSelectionProgram

variable {r Q : ℕ}

theorem inner_eval (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q) (u y : UniversalType r Q 1)
    (a : Data) (S : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : Cached a (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t u y)
    (hsize : ∀ j : Fin 256, j.val < 212 → (a.stacks j).length ≤ S) :
    let L := IntegerEntry.lengthBound R width.length (pairLength power) u y+power.1.length+1
    ∃ n ≤ IntegerEntry.budget aWord.length R width.length (pairLength power) power.1.length t u y+
        484*S+407*L+1073,
      ∃ rf result, Eval inner n a (finish a rf result) ∧
        pairValue result=IntegerEntry.value aWord.length R t u y ∧
        LayoutProgramScalar.wordTotal result ≤ constraintMassBound Q R ∧ pairLength result ≤ L := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end
