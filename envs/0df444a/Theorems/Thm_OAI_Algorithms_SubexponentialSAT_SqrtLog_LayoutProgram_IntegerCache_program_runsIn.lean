-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_IntegerCache_program_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:25:51.54554+00:00
-- url     : https://prove2.me/theorems/260a1aa8-b765-4291-a978-80fd18240a11
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramIntegerCache.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramIntegerCache.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open RowSelectionProgram LayoutProgramScalar`):
--
--   ```lean
--   theorem program_runsIn (regs : Fin 8 → Bool) (a r width : List Bool)
--       (hw : 1+2*a.length*r.length ≤ width.length) :
--       ∃ (rf : Fin 8 → Bool) (words : List (List Bool)),
--         RunsIn program
--           (7*(a.length+r.length+width.length)+flatCost a.length r.length width.length+11*r.length+27)
--           ((state regs a r width [] [] [] [] [] [] []).withPC (some program.entry))
--           ((state rf a r width [] [] width words.flatten
--             (List.replicate (r.length*width.length) false) (denominatorWord r.length) []).withPC none) ∧
--         words.length=r.length ∧ (∀ x∈words,x.length=width.length) ∧
--         words.map SubexponentialSAT.BinaryArithmetic.toNat=
--           (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) ∧
--         SubexponentialSAT.BinaryArithmetic.toNat (denominatorWord r.length)=2^(r.length-1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.H` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.denominatorWord` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.flatCost` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program` (definitions bundle `OAIQ081S143` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.state` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramIntegerCache.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program_runsIn)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S156

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram LayoutProgramScalar

theorem program_runsIn (regs : Fin 8 → Bool) (a r width : List Bool)
    (hw : 1+2*a.length*r.length ≤ width.length) :
    ∃ (rf : Fin 8 → Bool) (words : List (List Bool)),
      RunsIn program
        (7*(a.length+r.length+width.length)+flatCost a.length r.length width.length+11*r.length+27)
        ((state regs a r width [] [] [] [] [] [] []).withPC (some program.entry))
        ((state rf a r width [] [] width words.flatten
          (List.replicate (r.length*width.length) false) (denominatorWord r.length) []).withPC none) ∧
      words.length=r.length ∧ (∀ x∈words,x.length=width.length) ∧
      words.map SubexponentialSAT.BinaryArithmetic.toNat=
        (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) ∧
      SubexponentialSAT.BinaryArithmetic.toNat (denominatorWord r.length)=2^(r.length-1) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

end OAI.Algorithms
end
