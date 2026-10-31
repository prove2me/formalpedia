-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashQueryShadow_marked_shadow_bound_of_references
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow.marked_shadow_bound_of_references
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:16:04.360005+00:00
-- url     : https://prove2.me/theorems/666c4b10-44c7-472e-9d27-7b321e25a70e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow.marked_shadow_bound_of_references: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow.marked_shadow_bound_of_references` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryShadow.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryShadow.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow`, with `open BitProgram StructuredCalls SqrtLog ProgramTapeReplay`, `open HashMassAdapter HashGreedyExecution`):
--
--   ```lean
--   theorem marked_shadow_bound_of_references (base d a : State 40 896) (m depth L : ℕ)
--       (word tail : List Bool) (e : Fin m)
--       (hbase : ∀ i, (base.stacks i).length ≤ L)
--       (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
--         d.stacks i = base.stacks i)
--       (hhistory : (d.stacks 777).length ≤ L)
--       (hword : word.length = HashCandidates.payloadWidth m depth)
--       (hcounter : d.stacks 778 = Encoding.encodeList id [word])
--       (hscratch : d.stacks 779 = [])
--       (hcounterBound : 2 * HashCandidates.payloadWidth m depth + 3 ≤ L)
--       (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
--       (hready : Ready (fun ws => ws = workspace
--         (LeafOuterNative.trialStaged (trialState d m depth word))) a) :
--       ∀ i, ((rebaseState H (fun _ => [])
--         (RecordPrograms.state recordPorts a false true false tail
--           (Encoding.encodeNat e.val).reverse)).stacks i).length ≤ 3 * L + 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.state` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Index.alphabet` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay.rebaseState` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.payloadWidth` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.recordPorts` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution.trialState` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative.trialStaged` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.Ready` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.workspace` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.marked_with_shadow` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryShadow.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow.marked_shadow_bound_of_references)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow

open BitProgram StructuredCalls SqrtLog ProgramTapeReplay
open HashMassAdapter HashGreedyExecution

local notation "H" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322 ∨
  Fin.val i = 770 ∨ Fin.val i = 771 ∨ Fin.val i = 781)

theorem marked_shadow_bound_of_references (base d a : State 40 896) (m depth L : ℕ)
    (word tail : List Bool) (e : Fin m)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hhistory : (d.stacks 777).length ≤ L)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : d.stacks 778 = Encoding.encodeList id [word])
    (hscratch : d.stacks 779 = [])
    (hcounterBound : 2 * HashCandidates.payloadWidth m depth + 3 ≤ L)
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hready : Ready (fun ws => ws = workspace
      (LeafOuterNative.trialStaged (trialState d m depth word))) a) :
    ∀ i, ((rebaseState H (fun _ => [])
      (RecordPrograms.state recordPorts a false true false tail
        (Encoding.encodeNat e.val).reverse)).stacks i).length ≤ 3 * L + 2 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow
end
