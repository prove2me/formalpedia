-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_Numerator_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:06:19.614659+00:00
-- url     : https://prove2.me/theorems/e63251d0-82af-441a-88ba-e28d78072651
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramNumeratorRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramNumeratorRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes`, `open UniversalEntry RowSelectionProgram`, `open MatrixScanProgram MatrixEntryEvaluation MatrixEntryKernel MatrixExtendedEntryProgram`):
--
--   ```lean
--   theorem command_eval (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
--       (regs : Fin 10 → Bool) (a : List Bool) (R : ℕ) (t : Fin Q)
--       (u y : UniversalType r Q 1)
--       (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
--       (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
--       (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
--       (hwidth : Q+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) :
--       let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R a
--       ∃ n ≤ budget a.length R width.length (pairLength power) t u y,
--         ∃ rf result, Eval command n (state c regs t u y [] [] ([],[]))
--           (state c rf t u y [] [] result) ∧
--         pairValue result=value a.length R t u y ∧
--         LayoutProgramScalar.wordTotal result ≤ (8*Q)^(2*R) ∧
--         pairLength result ≤ (R-(unchangedCount (rows 0 u y)-1))*
--           LayoutProgramScalar.termGrowth (2*width.length+pairLength power)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.H` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termGrowth` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanProgram.unchangedCount` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.Saved` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryEvaluation.rows` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.budget` (definitions bundle `OAIQ081S073` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.value` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.state` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.unsignedSaved` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.command_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableProgram_runsIn` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramNumeratorRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval)

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

namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
open MatrixScanProgram MatrixEntryEvaluation MatrixEntryKernel MatrixExtendedEntryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

theorem command_eval (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (regs : Fin 10 → Bool) (a : List Bool) (R : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) :
    let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R a
    ∃ n ≤ budget a.length R width.length (pairLength power) t u y,
      ∃ rf result, Eval command n (state c regs t u y [] [] ([],[]))
        (state c rf t u y [] [] result) ∧
      pairValue result=value a.length R t u y ∧
      LayoutProgramScalar.wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-(unchangedCount (rows 0 u y)-1))*
        LayoutProgramScalar.termGrowth (2*width.length+pairLength power) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end
