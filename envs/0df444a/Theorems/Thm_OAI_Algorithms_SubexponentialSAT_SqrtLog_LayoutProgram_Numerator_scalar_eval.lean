-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_Numerator_scalar_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.scalar_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:07:06.222693+00:00
-- url     : https://prove2.me/theorems/e694147e-556f-492a-85b2-8c410f1cbfc8
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.scalar_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.scalar_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramNumeratorScalar.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramNumeratorScalar.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes`, `open UniversalEntry RowSelectionProgram`):
--
--   ```lean
--   theorem scalar_eval (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
--       (regs : Fin 10 → Bool) (a : List Bool) (R d : ℕ) (t : Fin Q)
--       (u y : UniversalType r Q 1) (h : List Bool)
--       (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
--       (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
--       (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
--       (hwidth : h.length+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) (hhQ : h.length ≤ Q) :
--       let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R a
--       ∃ n ≤ LayoutProgramScalar.FromCounts.totalCost a.length R d h.length width.length (pairLength power),
--         ∃ rf result, Eval scalar n (state c regs t u y (List.replicate (d+1) true) h ([],[]))
--           (state c rf t u y [] [] result) ∧
--         pairValue result=LayoutCoefficientAlgorithm.scalarSum a.length R d h.length ∧
--         LayoutProgramScalar.wordTotal result ≤ (8*Q)^(2*R) ∧
--         pairLength result ≤ (R-d)*LayoutProgramScalar.termGrowth (2*width.length+pairLength power)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarSum` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.H` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termGrowth` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.Saved` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.totalCost` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.state` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.unsignedSaved` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.scalar` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramNumeratorScalar.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.scalar_eval)

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
variable {r Q : ℕ}

theorem scalar_eval (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (regs : Fin 10 → Bool) (a : List Bool) (R d : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1) (h : List Bool)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hwidth : h.length+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) (hhQ : h.length ≤ Q) :
    let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R a
    ∃ n ≤ LayoutProgramScalar.FromCounts.totalCost a.length R d h.length width.length (pairLength power),
      ∃ rf result, Eval scalar n (state c regs t u y (List.replicate (d+1) true) h ([],[]))
        (state c rf t u y [] [] result) ∧
      pairValue result=LayoutCoefficientAlgorithm.scalarSum a.length R d h.length ∧
      LayoutProgramScalar.wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-d)*LayoutProgramScalar.termGrowth (2*width.length+pairLength power) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end
