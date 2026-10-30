-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CompileSpace_compile_word_answer_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_word_answer_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:43:36.884628+00:00
-- url     : https://prove2.me/theorems/bed96fd4-cfdd-4f12-9c3f-5bb6b94d9fea
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_word_answer_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_word_answer_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/CompileSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/CompileSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace`, with `open GuardedCompiler`, `open scoped BigOperators`):
--
--   ```lean
--   theorem compile_word_answer_space {r s l : ℕ} (p : BitProgram.Program r s l)
--       (countStack : Fin s) {input word : List Bool} {answer : Bool}
--       {final : BitProgram.Cfg r s l} {sourceSteps bound : ℕ}
--       (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
--       (halted : final.pc = none) (hword : final.stacks countStack = word)
--       (hanswer : final.stacks p.outputStack = [answer])
--       (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
--         BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
--         ∀ i, (intermediate.stacks i).length ≤ bound) :
--       ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
--         Computation.Trace (locatedStep (primitive p)) time
--           (locatedInit (primitive p) input) d ∧
--         d.config.state = .inl answer ∧
--         d.config.tapes countStack = Turing.Tape.mk₁ (word.map some) ∧
--         d.config.tapes p.outputStack = Turing.Tape.mk₁ [some answer] ∧
--         ∀ prefixSteps intermediate, prefixSteps ≤ time →
--           Computation.Trace (locatedStep (primitive p)) prefixSteps
--             (locatedInit (primitive p) input) intermediate →
--           visitedSpace intermediate ≤ s * (bound + input.length + 15)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace` and `OAI.Algorithms.SubexponentialSAT.BitProgram.initial` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler.primitive` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.Computation.Trace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LocatedCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.locatedInit`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.locatedStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.visitedSpace`, `OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine` and `OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine.Cfg` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.counting_primitive_from_entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/CompileSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_word_answer_space)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S043

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace

open GuardedCompiler
open scoped BigOperators

theorem compile_word_answer_space {r s l : ℕ} (p : BitProgram.Program r s l)
    (countStack : Fin s) {input word : List Bool} {answer : Bool}
    {final : BitProgram.Cfg r s l} {sourceSteps bound : ℕ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (halted : final.pc = none) (hword : final.stacks countStack = word)
    (hanswer : final.stacks p.outputStack = [answer])
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
      Computation.Trace (locatedStep (primitive p)) time
        (locatedInit (primitive p) input) d ∧
      d.config.state = .inl answer ∧
      d.config.tapes countStack = Turing.Tape.mk₁ (word.map some) ∧
      d.config.tapes p.outputStack = Turing.Tape.mk₁ [some answer] ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace (locatedStep (primitive p)) prefixSteps
          (locatedInit (primitive p) input) intermediate →
        visitedSpace intermediate ≤ s * (bound + input.length + 15) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace
end
