-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashMassSpace_collector_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.collector_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:14:52.199995+00:00
-- url     : https://prove2.me/theorems/a81cef57-a0f7-46c5-a70c-6e85b92fa32f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.collector_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.collector_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashMassSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashMassSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace`, with `open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram`, `open HashMassAdapter HashGreedyProgram.NativeRound`):
--
--   ```lean
--   theorem collector_space (query : Code) (count queryCost width : List Bool → ℕ)
--       (valid : List Bool → Prop) (a : HashMassAdapter.Data) (records : List (List Bool))
--       (L K : ℕ) (hL : ∀ i, (a.stacks i).length ≤ L)
--       (hsource : a.stacks 320 = Encoding.encodeList id records)
--       (h321 : a.stacks 321 = []) (h322 : a.stacks 322 = [])
--       (h323 : a.stacks 323 = []) (h324 : a.stacks 324 = [])
--       (hrecords : ∀ bits ∈ records, valid bits) (hgrowth : outputGrowth width records ≤ L)
--       (hq : ∀ bits tail (base : HashMassAdapter.Data), valid bits →
--         Ready (fun words => words = workspace a) base →
--         ∃ n middle, n ≤ queryCost bits ∧ workspace middle = workspace a ∧
--           read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
--           (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
--           Eval query n (state recordPorts base false true false tail bits.reverse)
--             (state recordPorts middle false true false tail []))
--       (hspace : ∀ bits tail base n middle, valid bits →
--         Ready (fun words => words = workspace a) base →
--         (read base).length ≤ L → tail.length ≤ L → bits.length ≤ L → width bits ≤ L →
--         Eval query n (state recordPorts base false true false tail bits.reverse)
--           (state recordPorts middle false true false tail []) →
--         StageSpace query n (state recordPorts base false true false tail bits.reverse) K)
--       {steps : ℕ} {b : HashMassAdapter.Data}
--       (he : Eval (.call (HashMassAdapter.program query)) steps a b) :
--       StageSpace (.call (HashMassAdapter.program query)) steps a
--         (max K (896 * L + 20 * (L + 1) + 10))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.outputGrowth` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.state` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.recordPorts` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.program` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.Data` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.read` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.workspace` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.mass_halt_space` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashMassSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.collector_space)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashMassAdapter HashGreedyProgram.NativeRound

theorem collector_space (query : Code) (count queryCost width : List Bool → ℕ)
    (valid : List Bool → Prop) (a : HashMassAdapter.Data) (records : List (List Bool))
    (L K : ℕ) (hL : ∀ i, (a.stacks i).length ≤ L)
    (hsource : a.stacks 320 = Encoding.encodeList id records)
    (h321 : a.stacks 321 = []) (h322 : a.stacks 322 = [])
    (h323 : a.stacks 323 = []) (h324 : a.stacks 324 = [])
    (hrecords : ∀ bits ∈ records, valid bits) (hgrowth : outputGrowth width records ≤ L)
    (hq : ∀ bits tail (base : HashMassAdapter.Data), valid bits →
      Ready (fun words => words = workspace a) base →
      ∃ n middle, n ≤ queryCost bits ∧ workspace middle = workspace a ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ bits tail base n middle, valid bits →
      Ready (fun words => words = workspace a) base →
      (read base).length ≤ L → tail.length ≤ L → bits.length ≤ L → width bits ≤ L →
      Eval query n (state recordPorts base false true false tail bits.reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query n (state recordPorts base false true false tail bits.reverse) K)
    {steps : ℕ} {b : HashMassAdapter.Data}
    (he : Eval (.call (HashMassAdapter.program query)) steps a b) :
    StageSpace (.call (HashMassAdapter.program query)) steps a
      (max K (896 * L + 20 * (L + 1) + 10)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace
end
