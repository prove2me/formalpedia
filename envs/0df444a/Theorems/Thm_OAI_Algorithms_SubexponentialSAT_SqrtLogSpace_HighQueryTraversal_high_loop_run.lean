-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryTraversal_high_loop_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal.high_loop_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:28:10.483633+00:00
-- url     : https://prove2.me/theorems/911d3e18-c6ad-45be-8de9-8831b60ef42d
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal.high_loop_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal.high_loop_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryTraversal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryTraversal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal`, with `open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram`, `open HighQueryAdapter PreparedBranchCount HighQueryLoop`, `open ExecCNFTupleEnumeration ExecCNFTupleOdometer`, `open HashGreedyProgram.NativeRound`):
--
--   ```lean
--   theorem high_loop_run
--       (stable : CounterForPrograms.FrameStable highPorts.counter (fun _ => I))
--       (width : 4*H.card+1≤B) (BD : B≤D)
--       (branch : ∀ (rank : ℕ), rank<2^H.card → ∀ (words : List (List Bool))
--         (a : HighQueryAdapter.Data), words.map List.length=List.replicate H.card 1 → I a →
--         a.stacks 789=Encoding.encodeList id words → a.stacks 790=[] →
--         a.stacks 791=[] → a.regs 21=true → CounterPrograms.value words.flatten=rank →
--         BinaryArithmetic.toNat (a.stacks 788)=rankSum (rankValue H hashes marked clause) 0 rank →
--         (a.stacks 788).length≤n+1 → (∀ i,(a.stacks i).length≤B) →
--         ∃ steps b, Eval HighQueryProgram.branch steps a b ∧ steps≤C ∧ I b ∧
--           BinaryArithmetic.toNat (b.stacks 788)=
--             rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
--           (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
--           b.stacks 789=a.stacks 789 ∧ b.stacks 790=a.stacks 790 ∧
--           (∀ i,(b.stacks i).length≤B) ∧
--           StageSpace HighQueryProgram.branch steps a D)
--       (a : HighQueryAdapter.Data) (hi : I a)
--       (hc : a.stacks 789=Encoding.encodeList id (List.replicate H.card [false]))
--       (hs : a.stacks 790=[]) (ht : a.stacks 791=[])
--       (hacc : BinaryArithmetic.toNat (a.stacks 788)=0)
--       (hlen : (a.stacks 788).length≤n+1) (hb : ∀ i,(a.stacks i).length≤B) :
--       ∃ steps b, Eval HighQueryProgram.highLoop steps a b ∧
--         steps+1≤2^H.card*(C+28*H.card+12)+3 ∧ I b ∧
--         BinaryArithmetic.toNat (b.stacks 788)=fullCount hashes marked clause ∧
--         (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
--         b.stacks 789=Encoding.encodeList id (List.replicate H.card [false]) ∧
--         b.stacks 790=[] ∧ b.regs 21=false ∧ (∀ i,(b.stacks i).length≤B) ∧
--         Trace (compiled HighQueryProgram.highLoop 789 788) (steps+1)
--           (a.withPC (some (compiled HighQueryProgram.highLoop 789 788).entry)) (b.withPC none) ∧
--         StageSpace HighQueryProgram.highLoop (steps+1) a (max D (40*(H.card+1)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.rankSum` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SparseRow` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.FrameStable` (definitions bundle `OAIQ081S066` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount.fullCount` (definitions bundle `OAIQ081S076` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.Data` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.Ports` (definitions bundle `OAIQ081S107` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount.rankValue` (definitions bundle `OAIQ081S127` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.highPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.branch` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.highLoop` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryTraversal.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal.high_loop_run)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount HighQueryLoop
open ExecCNFTupleEnumeration ExecCNFTupleOdometer
open HashGreedyProgram.NativeRound

variable {n : ℕ} (H : Finset (Fin n))
  (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
  (clause : List (SAT.Literal (Fin n)))
  (I : HighQueryAdapter.Data → Prop) (B C D : ℕ)

theorem high_loop_run
    (stable : CounterForPrograms.FrameStable highPorts.counter (fun _ => I))
    (width : 4*H.card+1≤B) (BD : B≤D)
    (branch : ∀ (rank : ℕ), rank<2^H.card → ∀ (words : List (List Bool))
      (a : HighQueryAdapter.Data), words.map List.length=List.replicate H.card 1 → I a →
      a.stacks 789=Encoding.encodeList id words → a.stacks 790=[] →
      a.stacks 791=[] → a.regs 21=true → CounterPrograms.value words.flatten=rank →
      BinaryArithmetic.toNat (a.stacks 788)=rankSum (rankValue H hashes marked clause) 0 rank →
      (a.stacks 788).length≤n+1 → (∀ i,(a.stacks i).length≤B) →
      ∃ steps b, Eval HighQueryProgram.branch steps a b ∧ steps≤C ∧ I b ∧
        BinaryArithmetic.toNat (b.stacks 788)=
          rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
        (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
        b.stacks 789=a.stacks 789 ∧ b.stacks 790=a.stacks 790 ∧
        (∀ i,(b.stacks i).length≤B) ∧
        StageSpace HighQueryProgram.branch steps a D)
    (a : HighQueryAdapter.Data) (hi : I a)
    (hc : a.stacks 789=Encoding.encodeList id (List.replicate H.card [false]))
    (hs : a.stacks 790=[]) (ht : a.stacks 791=[])
    (hacc : BinaryArithmetic.toNat (a.stacks 788)=0)
    (hlen : (a.stacks 788).length≤n+1) (hb : ∀ i,(a.stacks i).length≤B) :
    ∃ steps b, Eval HighQueryProgram.highLoop steps a b ∧
      steps+1≤2^H.card*(C+28*H.card+12)+3 ∧ I b ∧
      BinaryArithmetic.toNat (b.stacks 788)=fullCount hashes marked clause ∧
      (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
      b.stacks 789=Encoding.encodeList id (List.replicate H.card [false]) ∧
      b.stacks 790=[] ∧ b.regs 21=false ∧ (∀ i,(b.stacks i).length≤B) ∧
      Trace (compiled HighQueryProgram.highLoop 789 788) (steps+1)
        (a.withPC (some (compiled HighQueryProgram.highLoop 789 788).entry)) (b.withPC none) ∧
      StageSpace HighQueryProgram.highLoop (steps+1) a (max D (40*(H.card+1))) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal
end
