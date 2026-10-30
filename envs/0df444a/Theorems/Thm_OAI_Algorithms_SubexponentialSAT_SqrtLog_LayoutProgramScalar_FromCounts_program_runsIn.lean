-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgramScalar_FromCounts_program_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.program_runsIn
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:08:14.244601+00:00
-- url     : https://prove2.me/theorems/0ee90981-c783-4351-9c26-fa20c1f459ce
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.program_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.program_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarFromCounts.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarFromCounts.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram`, `open LayoutTriplePreparationProgram`):
--
--   ```lean
--   theorem program_runsIn (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
--       (regs : Fin 9 → Bool) (a h : List Bool) (R d Q : ℕ)
--       (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
--       (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
--       (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : wordTotal power=2^(R-1))
--       (hwidth : h.length+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) (hhQ : h.length ≤ Q) :
--       let c := unsignedSaved Hwords width power R a
--       ∃ rf result,
--         RunsIn program (totalCost a.length R d h.length width.length (pairLength power))
--           ((state c regs (List.replicate (d+1) true) h [] [] [] [] [] ([],[])).withPC (some program.entry))
--           ((state c rf [] [] [] [] [] [] [] result).withPC none) ∧
--         pairValue result=LayoutCoefficientAlgorithm.scalarSum a.length R d h.length ∧
--         wordTotal result ≤ (8*Q)^(2*R) ∧
--         pairLength result ≤ (R-d)*termGrowth (2*width.length+pairLength power)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarSum` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.H` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termGrowth` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.Saved` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.totalCost` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.state` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.unsignedSaved` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.program` (definitions bundle `OAIQ081S174` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.scalar_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramScalarFromCounts.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.program_runsIn)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

theorem program_runsIn (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (regs : Fin 9 → Bool) (a h : List Bool) (R d Q : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : wordTotal power=2^(R-1))
    (hwidth : h.length+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) (hhQ : h.length ≤ Q) :
    let c := unsignedSaved Hwords width power R a
    ∃ rf result,
      RunsIn program (totalCost a.length R d h.length width.length (pairLength power))
        ((state c regs (List.replicate (d+1) true) h [] [] [] [] [] ([],[])).withPC (some program.entry))
        ((state c rf [] [] [] [] [] [] [] result).withPC none) ∧
      pairValue result=LayoutCoefficientAlgorithm.scalarSum a.length R d h.length ∧
      wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-d)*termGrowth (2*width.length+pairLength power) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end
