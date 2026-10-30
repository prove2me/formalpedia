-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashCandidateProgram_Leaf_prepare_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.prepare_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:15:39.875596+00:00
-- url     : https://prove2.me/theorems/92a6126a-9f81-4dde-81cb-356b94ecfa3a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.prepare_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.prepare_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashCandidateProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashCandidateProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf`, with `open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram`, `open scoped BigOperators`):
--
--   ```lean
--   theorem prepare_eval {m depth : ℕ} (hm : 0 < m) (a : Data) (word : List Bool)
--       (hword : word.length = HashCandidates.payloadWidth m depth)
--       (hcounter : a.stacks 778 = Encoding.encodeList id [word])
--       (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 → a.stacks (loaderStacks j) = [])
--       (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = []) (ht : a.stacks 767 = [])
--       (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
--       (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m) :
--       ∃ n ≤ budget m depth, ∃ b, Eval prepare n a b ∧
--         b.stacks = Function.update a.stacks 768
--           (HashCandidates.normalize m depth word.reverse)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.loaderStacks` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.digitWidth`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.normalize` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.payloadWidth` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.prepare` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun.staged_boundary_attempt` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace.attempt_halt_space` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashCandidateProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.prepare_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog

namespace Leaf

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open scoped BigOperators

theorem prepare_eval {m depth : ℕ} (hm : 0 < m) (a : Data) (word : List Bool)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 → a.stacks (loaderStacks j) = [])
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = []) (ht : a.stacks 767 = [])
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m) :
    ∃ n ≤ budget m depth, ∃ b, Eval prepare n a b ∧
      b.stacks = Function.update a.stacks 768
        (HashCandidates.normalize m depth word.reverse) := by
  sorry

end Leaf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram
end
