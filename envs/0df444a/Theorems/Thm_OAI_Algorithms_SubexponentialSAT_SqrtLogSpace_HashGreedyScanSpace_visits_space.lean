-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyScanSpace_visits_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.visits_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:47:00.569127+00:00
-- url     : https://prove2.me/theorems/3c8172fd-01bc-4313-a842-a571733d5018
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.visits_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.visits_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyScanSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyScanSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace`, with `open BitProgram StructuredCalls SqrtLog`, `open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound`):
--
--   ```lean
--   theorem visits_space (mass : Cmd 40 896) (base : State 40 896)
--       (B C L K attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
--       (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
--       (hbase : ∀ i, (base.stacks i).length ≤ L)
--       (hB : B ≤ L) (hC : C ≤ L) (hcounter : 2 * C + 3 ≤ L)
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
--       {ranks : List ℕ} {steps : ℕ} {a b : State 40 896}
--       (hvis : ExecCNFTupleEnumeration.Visits counter (body mass) [C] ranks steps a b)
--       (ha : Boundary base B C a) (hs : a.stacks 779 = [])
--       (hc : (a.stacks 778).length = 2 * C + 3) :
--       ∀ k c, k ≤ steps →
--         Trace (compiled (ExecCNFTupleEnumeration.loopCmd counter (body mass)) 778 778) k
--           (a.withPC (some (compiled
--             (ExecCNFTupleEnumeration.loopCmd counter (body mass)) 778 778).entry)) c →
--         ∀ i, (c.stacks i).length ≤
--           max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.Fits` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.Visits` and `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.loopCmd` (definitions bundle `OAIQ081S082` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.attempt` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.body` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.Boundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.CoreClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.counter` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.scan_halt_space` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyScanSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.visits_space)

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

theorem visits_space (mass : Cmd 40 896) (base : State 40 896)
    (B C L K attemptCost : ℕ) (entry : ℕ → BinaryArgmin.Entry)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : B ≤ L) (hC : C ≤ L) (hcounter : 2 * C + 3 ≤ L)
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
    {ranks : List ℕ} {steps : ℕ} {a b : State 40 896}
    (hvis : ExecCNFTupleEnumeration.Visits counter (body mass) [C] ranks steps a b)
    (ha : Boundary base B C a) (hs : a.stacks 779 = [])
    (hc : (a.stacks 778).length = 2 * C + 3) :
    ∀ k c, k ≤ steps →
      Trace (compiled (ExecCNFTupleEnumeration.loopCmd counter (body mass)) 778 778) k
        (a.withPC (some (compiled
          (ExecCNFTupleEnumeration.loopCmd counter (body mass)) 778 778).entry)) c →
      ∀ i, (c.stacks i).length ≤
        max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace
end
