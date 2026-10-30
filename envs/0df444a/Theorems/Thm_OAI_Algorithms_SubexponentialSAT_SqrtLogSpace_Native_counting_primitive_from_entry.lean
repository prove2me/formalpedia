-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_counting_primitive_from_entry
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.counting_primitive_from_entry
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:17:58.054988+00:00
-- url     : https://prove2.me/theorems/90ad8554-896f-463a-8a17-bc2c5ee3ee9f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.counting_primitive_from_entry: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.counting_primitive_from_entry` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeOuter.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeOuter.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native`, with `open BitProgram StructuredCalls DisjointReuse`):
--
--   ```lean
--   theorem counting_primitive_from_entry {cutoff k n steps bound : ℕ}
--       (leaf : Cmd 80 1220) (F : SAT.CNF (Fin n)) (b : State 80 1220)
--       (he : DFSVisit.BoundedEval (entryCommand cutoff (outerCommand k leaf)) steps
--         (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b bound)
--       (hc : b.stacks ABI.countStack = countWord (SAT.count F))
--       (ha : b.stacks ABI.answerStack = [decide (0 < SAT.count F)]) :
--       ∃ time : ℕ, ∃ final : LocatedCfg (GuardedCompiler.primitive (countingProgram cutoff k leaf)),
--         Computation.Trace
--           (locatedStep (GuardedCompiler.primitive (countingProgram cutoff k leaf))) time
--           (locatedInit (GuardedCompiler.primitive (countingProgram cutoff k leaf))
--             (Encoding.encodeCNF F)) final ∧
--         final.config.state = .inl (decide (0 < SAT.count F)) ∧
--         final.config.tapes ABI.countStack =
--           Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
--         final.config.tapes ABI.answerStack =
--           Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
--         time ≤ 7 * (steps + 1) ∧
--         ∀ prefixSteps intermediate, prefixSteps ≤ time →
--           Computation.Trace
--             (locatedStep (GuardedCompiler.primitive (countingProgram cutoff k leaf))) prefixSteps
--             (locatedInit (GuardedCompiler.primitive (countingProgram cutoff k leaf))
--               (Encoding.encodeCNF F)) intermediate →
--           visitedSpace intermediate ≤ 1220 * (bound + Encoding.formulaBitLength F + 15)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI.answerStack` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI.countStack` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredProgram.ioState` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler.primitive` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entryCommand` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.countingProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outerCommand` (definitions bundle `OAIQ081S152` of this split); `OAI.Algorithms.SubexponentialSAT.Computation.Trace`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeCNF`, `OAI.Algorithms.SubexponentialSAT.Encoding.formulaBitLength`, `OAI.Algorithms.SubexponentialSAT.SAT.CNF`, `OAI.Algorithms.SubexponentialSAT.SAT.count`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LocatedCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.locatedInit`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.locatedStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.visitedSpace`, `OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine` and `OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine.Cfg` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeOuter.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.counting_primitive_from_entry)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S152

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse

theorem counting_primitive_from_entry {cutoff k n steps bound : ℕ}
    (leaf : Cmd 80 1220) (F : SAT.CNF (Fin n)) (b : State 80 1220)
    (he : DFSVisit.BoundedEval (entryCommand cutoff (outerCommand k leaf)) steps
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b bound)
    (hc : b.stacks ABI.countStack = countWord (SAT.count F))
    (ha : b.stacks ABI.answerStack = [decide (0 < SAT.count F)]) :
    ∃ time : ℕ, ∃ final : LocatedCfg (GuardedCompiler.primitive (countingProgram cutoff k leaf)),
      Computation.Trace
        (locatedStep (GuardedCompiler.primitive (countingProgram cutoff k leaf))) time
        (locatedInit (GuardedCompiler.primitive (countingProgram cutoff k leaf))
          (Encoding.encodeCNF F)) final ∧
      final.config.state = .inl (decide (0 < SAT.count F)) ∧
      final.config.tapes ABI.countStack =
        Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
      final.config.tapes ABI.answerStack =
        Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
      time ≤ 7 * (steps + 1) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace
          (locatedStep (GuardedCompiler.primitive (countingProgram cutoff k leaf))) prefixSteps
          (locatedInit (GuardedCompiler.primitive (countingProgram cutoff k leaf))
            (Encoding.encodeCNF F)) intermediate →
        visitedSpace intermediate ≤ 1220 * (bound + Encoding.formulaBitLength F + 15) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end
