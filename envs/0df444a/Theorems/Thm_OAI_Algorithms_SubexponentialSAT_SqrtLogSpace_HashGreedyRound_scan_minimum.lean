-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyRound_scan_minimum
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.scan_minimum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:45:51.43259+00:00
-- url     : https://prove2.me/theorems/b41c68ae-6078-423b-a6d7-bac823a0d335
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.scan_minimum: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.scan_minimum` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyRound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyRound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound`, with `open BitProgram StructuredCalls SqrtLog`, `open HashGreedyProgram HashGreedyProgram.NativeRound`):
--
--   ```lean
--   theorem scan_minimum (mass : Cmd 40 896) (base : State 40 896)
--       (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
--       (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
--       (hcounter : base.stacks 778 = Encoding.encodeList id [List.replicate C false])
--       (hscratch : base.stacks 779 = []) (hseed : readEntry 770 771 base = entry 0)
--       (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
--       (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
--         a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
--         ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
--           b.stacks = Function.update (Function.update a.stacks 768
--             (entry (CounterPrograms.value words.flatten)).payload) 769
--             (entry (CounterPrograms.value words.flatten)).score) :
--       ∃ n ≤ 2 ^ C * (attemptCost + (100 * (B + C + 1) + 1) + 7 * (2 * C + 3) + 5) + 2,
--         ∃ b, Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) n base b ∧
--           Boundary base B C b ∧ b.stacks 779 = [] ∧
--           b.stacks 778 = Encoding.encodeList id [List.replicate C false] ∧
--           (∃ j < 2 ^ C, readEntry 770 771 b = entry j) ∧
--           (∀ j < 2 ^ C, BinaryArgmin.value (readEntry 770 771 b) ≤ BinaryArgmin.value (entry j)) ∧
--           readEntry 770 771 b = HashSelect.best BinaryArgmin.value (entry 0)
--             ((List.range' 0 (2 ^ C)).map entry)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.Fits` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.best` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.value` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.enumerate` (definitions bundle `OAIQ081S082` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.attempt` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.body` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.readEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.Boundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.CoreClean` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.counter` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.rounds_halt_space` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.ready_rounds` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyRound.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.scan_minimum)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

theorem scan_minimum (mass : Cmd 40 896) (base : State 40 896)
    (B C attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hcounter : base.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : base.stacks 779 = []) (hseed : readEntry 770 771 base = entry 0)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score) :
    ∃ n ≤ 2 ^ C * (attemptCost + (100 * (B + C + 1) + 1) + 7 * (2 * C + 3) + 5) + 2,
      ∃ b, Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) n base b ∧
        Boundary base B C b ∧ b.stacks 779 = [] ∧
        b.stacks 778 = Encoding.encodeList id [List.replicate C false] ∧
        (∃ j < 2 ^ C, readEntry 770 771 b = entry j) ∧
        (∀ j < 2 ^ C, BinaryArgmin.value (readEntry 770 771 b) ≤ BinaryArgmin.value (entry j)) ∧
        readEntry 770 771 b = HashSelect.best BinaryArgmin.value (entry 0)
          ((List.range' 0 (2 ^ C)).map entry) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound
end
