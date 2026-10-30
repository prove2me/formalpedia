-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCandidate_attempt_entry_of_query
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.attempt_entry_of_query
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:16:45.133425+00:00
-- url     : https://prove2.me/theorems/bf60b636-41c0-4387-890d-2094009c390d
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.attempt_entry_of_query: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.attempt_entry_of_query` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCandidate.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCandidate.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate`, with `open BitProgram StructuredCalls SqrtLog`, `open HashGreedyProgram HashGreedyProgram.NativeRound`):
--
--   ```lean
--   theorem attempt_entry_of_query {X : Type*} [Fintype X]
--       (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
--       (n m depth : ℕ) (rows : List (List Bool)) (mass : Cmd 40 896)
--       (a b c : State 40 896) (np nq : ℕ) (word score : List Bool)
--       (hword : word.length = HashCandidates.payloadWidth m depth)
--       (hp : Eval HashCandidateProgram.Leaf.prepare np a b)
--       (hprep : b.stacks = Function.update a.stacks 768
--         (HashCandidates.normalize m depth word.reverse))
--       (hq : Eval mass nq b c) (hquery : c.stacks = Function.update b.stacks 769 score)
--       (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
--       (hshape : (a.stacks 818).length = HashSelect.loopCap n m)
--       (hlen : score.length ≤ HashSelect.loopCap n m)
--       (hvalue : BinaryArithmetic.toNat score = HashSelect.mass rowAccept weight
--         (HashCandidates.normalize m depth word.reverse :: rows)) :
--       ∃ d, Eval (attempt mass) (np + (nq + (23 * HashSelect.loopCap n m + 20))) a d ∧
--         d.stacks = Function.update (Function.update a.stacks 768
--           (entry rowAccept weight n m depth rows (CounterPrograms.value word)).payload) 769
--           (entry rowAccept weight n m depth rows (CounterPrograms.value word)).score
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.Entry` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.mass` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.normalize` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.payloadWidth` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.prepare` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.attempt` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun.staged_boundary_attempt` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashGreedyCandidate.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.attempt_entry_of_query)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

theorem attempt_entry_of_query {X : Type*} [Fintype X]
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m depth : ℕ) (rows : List (List Bool)) (mass : Cmd 40 896)
    (a b c : State 40 896) (np nq : ℕ) (word score : List Bool)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hp : Eval HashCandidateProgram.Leaf.prepare np a b)
    (hprep : b.stacks = Function.update a.stacks 768
      (HashCandidates.normalize m depth word.reverse))
    (hq : Eval mass nq b c) (hquery : c.stacks = Function.update b.stacks 769 score)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (hshape : (a.stacks 818).length = HashSelect.loopCap n m)
    (hlen : score.length ≤ HashSelect.loopCap n m)
    (hvalue : BinaryArithmetic.toNat score = HashSelect.mass rowAccept weight
      (HashCandidates.normalize m depth word.reverse :: rows)) :
    ∃ d, Eval (attempt mass) (np + (nq + (23 * HashSelect.loopCap n m + 20))) a d ∧
      d.stacks = Function.update (Function.update a.stacks 768
        (entry rowAccept weight n m depth rows (CounterPrograms.value word)).payload) 769
        (entry rowAccept weight n m depth rows (CounterPrograms.value word)).score := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
end
