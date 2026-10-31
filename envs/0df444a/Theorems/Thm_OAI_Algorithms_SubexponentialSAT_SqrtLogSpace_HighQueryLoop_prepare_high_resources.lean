-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryLoop_prepare_high_resources
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.prepare_high_resources
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:39:32.474059+00:00
-- url     : https://prove2.me/theorems/955c4fba-2072-456b-b8ec-9fe93e6aab46
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.prepare_high_resources: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.prepare_high_resources` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryDecode.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryDecode.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop`, with `open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram`, `open HighQueryAdapter PreparedBranchCount`, `open HashGreedyProgram.NativeRound`):
--
--   ```lean
--   theorem prepare_high_resources {n : ℕ} (H : Finset (Fin n)) (words : List (List Bool))
--       (hshape : words.map List.length=List.replicate H.card 1)
--       (rank : Fin (2^H.card)) (hrank : CounterPrograms.value words.flatten=rank.val)
--       (a : Data) (P B : ℕ)
--       (hc : a.stacks 330=Encoding.encodeList id words)
--       (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
--       (hcounter : (a.stacks 330).length≤P) (hmask : (a.stacks 338).length≤P)
--       (hchanged : ∀ i∈highChanged,(a.stacks i).length≤P)
--       (hB : ∀ i,(a.stacks i).length≤B) :
--       ∃ steps rf, let b := highResult (resetHighState a) rf words.flatten
--         Eval prepareHigh steps a b ∧ steps≤18*P+65*n+67 ∧
--         b.stacks 702=List.ofFn (fun v : Fin n => decide (v∈H)) ∧
--         b.stacks 703=List.ofFn (HighIncidence.glue H
--           (SqrtLog.HighIncidenceProgram.Rank.highEquiv
--             (SqrtLog.HighIncidenceProgram.Order.highOrder H) rank) (fun _ => false)) ∧
--         (∀ i,i∉highChanged → b.stacks i=a.stacks i) ∧
--         (∀ i,(b.stacks i).length≤B) ∧
--         StageSpace prepareHigh (steps+1) a (max (67*P+37) B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.highOrder` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.highChanged` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.Data` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank.highEquiv` (definitions bundle `OAIQ081S102` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.highResult` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.prepareHigh` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.resetHighState` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryDecode.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.prepare_high_resources)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount
open HashGreedyProgram.NativeRound

theorem prepare_high_resources {n : ℕ} (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1)
    (rank : Fin (2^H.card)) (hrank : CounterPrograms.value words.flatten=rank.val)
    (a : Data) (P B : ℕ)
    (hc : a.stacks 330=Encoding.encodeList id words)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hcounter : (a.stacks 330).length≤P) (hmask : (a.stacks 338).length≤P)
    (hchanged : ∀ i∈highChanged,(a.stacks i).length≤P)
    (hB : ∀ i,(a.stacks i).length≤B) :
    ∃ steps rf, let b := highResult (resetHighState a) rf words.flatten
      Eval prepareHigh steps a b ∧ steps≤18*P+65*n+67 ∧
      b.stacks 702=List.ofFn (fun v : Fin n => decide (v∈H)) ∧
      b.stacks 703=List.ofFn (HighIncidence.glue H
        (SqrtLog.HighIncidenceProgram.Rank.highEquiv
          (SqrtLog.HighIncidenceProgram.Order.highOrder H) rank) (fun _ => false)) ∧
      (∀ i,i∉highChanged → b.stacks i=a.stacks i) ∧
      (∀ i,(b.stacks i).length≤B) ∧
      StageSpace prepareHigh (steps+1) a (max (67*P+37) B) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
end
