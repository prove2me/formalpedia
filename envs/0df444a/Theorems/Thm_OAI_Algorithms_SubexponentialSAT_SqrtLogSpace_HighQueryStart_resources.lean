-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryStart_resources
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart.resources
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:39:25.10419+00:00
-- url     : https://prove2.me/theorems/9a01528a-d03b-42ca-9be1-30299f84abf6
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart.resources: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart.resources` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryStart.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryStart.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart`, with `open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram`, `open LeafProgram.Query HashGreedyProgram.NativeRound`):
--
--   ```lean
--   theorem resources (q : LeafQueryFrontend.Query) (a : Data) (L B D : ℕ)
--       (hm : a.stacks 338 =
--         LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient))
--       (hL : ∀ i ∈ HighQueryLocalBounds.seedSources, (a.stacks i).length ≤ L)
--       (hlocal : 12 * L + 5 ≤ D) (hD : ∀ i, (a.stacks i).length ≤ D)
--       (hn : 4 * BinaryArithmetic.toNat q.ambient + 1 ≤ B)
--       (hframe : ∀ i, i ∉ changed → (a.stacks i).length ≤ B) :
--       ∃ steps rf, steps ≤ 110 * L + 80 ∧
--         Eval command steps a (HighCountSeed.initialized a rf) ∧
--         Trace (compiled command 778 777) (steps + 1)
--           (a.withPC (some (compiled command 778 777).entry))
--           ((HighCountSeed.initialized a rf).withPC none) ∧
--         (∀ t z, t ≤ steps + 1 → Trace (compiled command 778 777) t
--           (a.withPC (some (compiled command 778 777).entry)) z →
--           ∀ i, (z.stacks i).length ≤ D) ∧
--         (∀ i, ((HighCountSeed.initialized a rf).stacks i).length ≤ B) ∧
--         (HighCountSeed.initialized a rf).stacks 789 =
--           Encoding.encodeList id (List.replicate (HighMarkedFrontend.highSet q).card [false]) ∧
--         (∀ i ∈ ([788,790,323,791,792] : List (Fin 896)),
--           (HighCountSeed.initialized a rf).stacks i = []) ∧
--         (HighCountSeed.initialized a rf).regs 21 = true ∧
--         (∀ i, HashMarkedReturn.kept i = true →
--           (HighCountSeed.initialized a rf).stacks i = a.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.kept`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds.seedSources` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart.changed` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highMask` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart.Data` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.scopeRows` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initialized`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.highSet` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart.command` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.prepare_seed` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryStart.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart.resources)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound

theorem resources (q : LeafQueryFrontend.Query) (a : Data) (L B D : ℕ)
    (hm : a.stacks 338 =
      LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient))
    (hL : ∀ i ∈ HighQueryLocalBounds.seedSources, (a.stacks i).length ≤ L)
    (hlocal : 12 * L + 5 ≤ D) (hD : ∀ i, (a.stacks i).length ≤ D)
    (hn : 4 * BinaryArithmetic.toNat q.ambient + 1 ≤ B)
    (hframe : ∀ i, i ∉ changed → (a.stacks i).length ≤ B) :
    ∃ steps rf, steps ≤ 110 * L + 80 ∧
      Eval command steps a (HighCountSeed.initialized a rf) ∧
      Trace (compiled command 778 777) (steps + 1)
        (a.withPC (some (compiled command 778 777).entry))
        ((HighCountSeed.initialized a rf).withPC none) ∧
      (∀ t z, t ≤ steps + 1 → Trace (compiled command 778 777) t
        (a.withPC (some (compiled command 778 777).entry)) z →
        ∀ i, (z.stacks i).length ≤ D) ∧
      (∀ i, ((HighCountSeed.initialized a rf).stacks i).length ≤ B) ∧
      (HighCountSeed.initialized a rf).stacks 789 =
        Encoding.encodeList id (List.replicate (HighMarkedFrontend.highSet q).card [false]) ∧
      (∀ i ∈ ([788,790,323,791,792] : List (Fin 896)),
        (HighCountSeed.initialized a rf).stacks i = []) ∧
      (HighCountSeed.initialized a rf).regs 21 = true ∧
      (∀ i, HashMarkedReturn.kept i = true →
        (HighCountSeed.initialized a rf).stacks i = a.stacks i) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart
end
