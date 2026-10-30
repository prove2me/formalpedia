-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyScanSpace_scan_halt_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.scan_halt_space
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:46:32.623223+00:00
-- url     : https://prove2.me/theorems/309c408f-3b0a-4b6d-87ce-3ffc6dcbddcd
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.scan_halt_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.scan_halt_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyScanSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyScanSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace`, with `open BitProgram StructuredCalls SqrtLog`, `open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound`):
--
--   ```lean
--   theorem scan_halt_space (mass : Cmd 40 896) (base : State 40 896)
--       (B C L K attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
--       (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
--       (hbase : ∀ i, (base.stacks i).length ≤ L)
--       (hB : B ≤ L) (hC : C ≤ L) (hcounterBound : 2 * C + 3 ≤ L)
--       (hcounter : base.stacks 778 = Encoding.encodeList id [List.replicate C false])
--       (hscratch : base.stacks 779 = []) (hseed : readEntry 770 771 base = entry 0)
--       (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
--       (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
--         a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
--         ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
--           b.stacks = Function.update (Function.update a.stacks 768
--             (entry (CounterPrograms.value words.flatten)).payload) 769
--             (entry (CounterPrograms.value words.flatten)).score)
--       (hspace : ∀ words a n b, words.map List.length = [C] → Boundary base B C a →
--         a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
--         Eval (attempt mass) n a b → StageSpace (attempt mass) n a K)
--       {steps : ℕ} {b : State 40 896}
--       (he : Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) steps base b) :
--       StageSpace (ExecCNFTupleEnumeration.enumerate counter (body mass)) (steps + 1) base
--         (max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.Fits` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.enumerate` (definitions bundle `OAIQ081S082` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.attempt` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.body` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.readEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.Boundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.CoreClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.counter` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.rounds_halt_space` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyScanSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.scan_halt_space)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound

theorem scan_halt_space (mass : Cmd 40 896) (base : State 40 896)
    (B C L K attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : B ≤ L) (hC : C ≤ L) (hcounterBound : 2 * C + 3 ≤ L)
    (hcounter : base.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : base.stacks 779 = []) (hseed : readEntry 770 771 base = entry 0)
    (hfit : ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry j))
    (hattempt : ∀ words a, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 768
          (entry (CounterPrograms.value words.flatten)).payload) 769
          (entry (CounterPrograms.value words.flatten)).score)
    (hspace : ∀ words a n b, words.map List.length = [C] → Boundary base B C a →
      a.stacks 778 = Encoding.encodeList id words → a.stacks 779 = [] →
      Eval (attempt mass) n a b → StageSpace (attempt mass) n a K)
    {steps : ℕ} {b : State 40 896}
    (he : Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) steps base b) :
    StageSpace (ExecCNFTupleEnumeration.enumerate counter (body mass)) (steps + 1) base
      (max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace
end
