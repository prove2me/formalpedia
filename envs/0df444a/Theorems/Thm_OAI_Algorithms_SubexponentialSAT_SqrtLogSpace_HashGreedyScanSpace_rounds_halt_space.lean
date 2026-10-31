-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyScanSpace_rounds_halt_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.rounds_halt_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:45:44.753475+00:00
-- url     : https://prove2.me/theorems/04ef1477-c3d1-4a7c-a264-caa1cd551933
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.rounds_halt_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.rounds_halt_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyScanSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyScanSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace`, with `open BitProgram StructuredCalls SqrtLog`, `open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound`):
--
--   ```lean
--   theorem rounds_halt_space (mass : Cmd 40 896) (base : State 40 896)
--       (B C L K attemptCost count : ℕ) (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
--       (initial : List (List Bool)) (hhistory : base.stacks 777 = encodedHistory initial)
--       (hdepth : (base.stacks 781).length = count)
--       (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
--       (hbp : base.stacks 770 = []) (hbs : base.stacks 771 = [])
--       (hbase : ∀ i, (base.stacks i).length ≤ L)
--       (hB : B ≤ L) (hC : C ≤ L) (hcounterBound : 2 * C + 3 ≤ L)
--       (hhistoryBound : (encodedHistory initial).length + count * (2 * C + 2) ≤ L)
--       (hcounter : base.stacks 778 = Encoding.encodeList id [List.replicate C false])
--       (hscratch : base.stacks 779 = [])
--       (hfit : ∀ rows, rows.length ≤ initial.length + count →
--         ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j))
--       (hattempt : ∀ rows a, rows.length ≤ initial.length + count → RowBoundary base rows a →
--         (∃ q ≤ count, rows = HashSelectProgram.iter (nextRows entry C) q initial) →
--         (encodedHistory rows).length ≤ (encodedHistory initial).length + count * (2 * C + 2) →
--         ∀ words d, words.map List.length = [C] →
--         (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
--         d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
--         ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n d b ∧
--           b.stacks = Function.update (Function.update d.stacks 768
--             (entry rows (CounterPrograms.value words.flatten)).payload) 769
--             (entry rows (CounterPrograms.value words.flatten)).score)
--       (hspace : ∀ rows a, rows.length ≤ initial.length + count → RowBoundary base rows a →
--         (∃ q ≤ count, rows = HashSelectProgram.iter (nextRows entry C) q initial) →
--         (encodedHistory rows).length ≤ (encodedHistory initial).length + count * (2 * C + 2) →
--         ∀ words d n b, words.map List.length = [C] →
--         (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
--         d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
--         (∀ i, (d.stacks i).length ≤ L) →
--         Eval (attempt mass) n d b → StageSpace (attempt mass) n d K)
--       {steps : ℕ} {b : State 40 896} (he : Eval (NativeRound.rounds mass) steps base b) :
--       StageSpace (NativeRound.rounds mass) (steps + 1) base
--         (max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.Fits` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.iter` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.nextRows` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.encodedHistory` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.attempt` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.RowBoundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.CoreClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.rounds` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.ready_rounds` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyScanSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.rounds_halt_space)

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

theorem rounds_halt_space (mass : Cmd 40 896) (base : State 40 896)
    (B C L K attemptCost count : ℕ) (entry : List (List Bool) → ℕ → BinaryArgmin.Entry)
    (initial : List (List Bool)) (hhistory : base.stacks 777 = encodedHistory initial)
    (hdepth : (base.stacks 781).length = count)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hbp : base.stacks 770 = []) (hbs : base.stacks 771 = [])
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hB : B ≤ L) (hC : C ≤ L) (hcounterBound : 2 * C + 3 ≤ L)
    (hhistoryBound : (encodedHistory initial).length + count * (2 * C + 2) ≤ L)
    (hcounter : base.stacks 778 = Encoding.encodeList id [List.replicate C false])
    (hscratch : base.stacks 779 = [])
    (hfit : ∀ rows, rows.length ≤ initial.length + count →
      ∀ j < 2 ^ C, BinaryArgmin.Fits B C (entry rows j))
    (hattempt : ∀ rows a, rows.length ≤ initial.length + count → RowBoundary base rows a →
      (∃ q ≤ count, rows = HashSelectProgram.iter (nextRows entry C) q initial) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length + count * (2 * C + 2) →
      ∀ words d, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      ∃ n ≤ attemptCost, ∃ b, Eval (attempt mass) n d b ∧
        b.stacks = Function.update (Function.update d.stacks 768
          (entry rows (CounterPrograms.value words.flatten)).payload) 769
          (entry rows (CounterPrograms.value words.flatten)).score)
    (hspace : ∀ rows a, rows.length ≤ initial.length + count → RowBoundary base rows a →
      (∃ q ≤ count, rows = HashSelectProgram.iter (nextRows entry C) q initial) →
      (encodedHistory rows).length ≤ (encodedHistory initial).length + count * (2 * C + 2) →
      ∀ words d n b, words.map List.length = [C] →
      (∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i) →
      d.stacks 778 = Encoding.encodeList id words → d.stacks 779 = [] →
      (∀ i, (d.stacks i).length ≤ L) →
      Eval (attempt mass) n d b → StageSpace (attempt mass) n d K)
    {steps : ℕ} {b : State 40 896} (he : Eval (NativeRound.rounds mass) steps base b) :
    StageSpace (NativeRound.rounds mass) (steps + 1) base
      (max K (896 * L + 100 * (B + C + 1) + 7 * (2 * C + 3) + 20)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace
end
