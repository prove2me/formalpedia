-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLargeEntry_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:30:19.098117+00:00
-- url     : https://prove2.me/theorems/c5b9242f-eff3-4191-9bfe-16dfd7806375
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLargeEntry.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLargeEntry.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry`, with `open BitProgram StructuredCalls DisjointReuse SqrtLog.Statement NativeOuterBudgets`):
--
--   ```lean
--   theorem run (k : ℕ) (hk : 2 ≤ k) :
--       ∃ cutoff : ℕ, ∃ C A : ℝ, ∃ d S e : ℕ, 1 ≤ C ∧ 1 ≤ A ∧
--         ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F → cutoff < n →
--         ∃ time : ℕ, ∃ final : LocatedCfg
--           (GuardedCompiler.primitive (Native.countingProgram cutoff k (NativeLeafProgram.command k))),
--           Computation.Trace
--             (locatedStep (GuardedCompiler.primitive
--               (Native.countingProgram cutoff k (NativeLeafProgram.command k)))) time
--             (locatedInit (GuardedCompiler.primitive
--               (Native.countingProgram cutoff k (NativeLeafProgram.command k)))
--               (Encoding.encodeCNF F)) final ∧
--           final.config.state = .inl (decide (0 < SAT.count F)) ∧
--           final.config.tapes ABI.countStack =
--             Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
--           final.config.tapes ABI.answerStack =
--             Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
--           (time : ℝ) ≤ runtimeBound C A d (Encoding.formulaBitLength F) n ∧
--           ∀ prefixSteps intermediate, prefixSteps ≤ time →
--             Computation.Trace
--               (locatedStep (GuardedCompiler.primitive
--                 (Native.countingProgram cutoff k (NativeLeafProgram.command k)))) prefixSteps
--               (locatedInit (GuardedCompiler.primitive
--                 (Native.countingProgram cutoff k (NativeLeafProgram.command k)))
--                 (Encoding.encodeCNF F)) intermediate →
--             visitedSpace intermediate ≤ S * (Encoding.formulaBitLength F + 1) ^ e
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI.answerStack` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI.countStack` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler.primitive` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entryCommand` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.countingProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outerCommand` (definitions bundle `OAIQ081S152` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram.command` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.Computation.Trace`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeCNF`, `OAI.Algorithms.SubexponentialSAT.Encoding.formulaBitLength`, `OAI.Algorithms.SubexponentialSAT.SAT.CNF`, `OAI.Algorithms.SubexponentialSAT.SAT.WidthAtMost`, `OAI.Algorithms.SubexponentialSAT.SAT.count`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LocatedCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.locatedInit`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.locatedStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.visitedSpace`, `OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound` and `OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine.Cfg` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLargeEntry.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry

open BitProgram StructuredCalls DisjointReuse SqrtLog.Statement NativeOuterBudgets

theorem run (k : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∃ C A : ℝ, ∃ d S e : ℕ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F → cutoff < n →
      ∃ time : ℕ, ∃ final : LocatedCfg
        (GuardedCompiler.primitive (Native.countingProgram cutoff k (NativeLeafProgram.command k))),
        Computation.Trace
          (locatedStep (GuardedCompiler.primitive
            (Native.countingProgram cutoff k (NativeLeafProgram.command k)))) time
          (locatedInit (GuardedCompiler.primitive
            (Native.countingProgram cutoff k (NativeLeafProgram.command k)))
            (Encoding.encodeCNF F)) final ∧
        final.config.state = .inl (decide (0 < SAT.count F)) ∧
        final.config.tapes ABI.countStack =
          Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
        final.config.tapes ABI.answerStack =
          Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
        (time : ℝ) ≤ runtimeBound C A d (Encoding.formulaBitLength F) n ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ time →
          Computation.Trace
            (locatedStep (GuardedCompiler.primitive
              (Native.countingProgram cutoff k (NativeLeafProgram.command k)))) prefixSteps
            (locatedInit (GuardedCompiler.primitive
              (Native.countingProgram cutoff k (NativeLeafProgram.command k)))
              (Encoding.encodeCNF F)) intermediate →
          visitedSpace intermediate ≤ S * (Encoding.formulaBitLength F + 1) ^ e := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry
end
