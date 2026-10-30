-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSRefinement_accumulate_after_leaf
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.accumulate_after_leaf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:03:35.15393+00:00
-- url     : https://prove2.me/theorems/f8015f15-f044-4a6a-b1c5-d0cc94fb96fc
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.accumulate_after_leaf: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.accumulate_after_leaf` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/CountDFS.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/CountDFS.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement`, with `open SAT SparsePriorityProgram BitProgram StructuredCalls`):
--
--   ```lean
--   theorem accumulate_after_leaf (threshold : List Bool) (node : Node n)
--       (rest : List (Node n)) (total bound : ℕ) (d : SparseDFSProgram.Data)
--       (hpending : d.stacks 257 = pendingBytes rest)
--       (hheader : d.stacks 258 = Encoding.encodeNat n)
--       (hthreshold : d.stacks 259 = threshold)
--       (htotal : d.stacks 260 = binaryNat total)
--       (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
--       (hleaf : d.stacks 263 = binaryNat (rawCount node.formula))
--       (hscratch : d.stacks 30 = [])
--       (hcount : total + rawCount node.formula ≤ 2 ^ n)
--       (hbound : ∀ i, (d.stacks i).length ≤ bound) :
--       ∃ t ≤ 100 * (n + 1), ∃ e,
--         Eval SparseDFSProgram.accumulate t d e ∧
--         AfterVisit threshold ⟨rest, total + rawCount node.formula⟩ e ∧
--         (∀ i, i ≠ 260 → i ≠ 263 → i ≠ 30 → e.stacks i = d.stacks i) ∧
--         ∀ prefixSteps c, prefixSteps ≤ t →
--           Trace (compiled SparseDFSProgram.accumulate 256 256) prefixSteps
--             (d.withPC (some (compiled SparseDFSProgram.accumulate 256 256).entry)) c →
--           ∀ i, (c.stacks i).length ≤ max (100 * (n + 1)) bound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.binaryNat` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.rawCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Node`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.pendingBytes` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Frontier` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.accumulate` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.AfterVisit` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/CountDFS.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.accumulate_after_leaf)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement

open SAT SparsePriorityProgram BitProgram StructuredCalls

variable {n : ℕ}

theorem accumulate_after_leaf (threshold : List Bool) (node : Node n)
    (rest : List (Node n)) (total bound : ℕ) (d : SparseDFSProgram.Data)
    (hpending : d.stacks 257 = pendingBytes rest)
    (hheader : d.stacks 258 = Encoding.encodeNat n)
    (hthreshold : d.stacks 259 = threshold)
    (htotal : d.stacks 260 = binaryNat total)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hleaf : d.stacks 263 = binaryNat (rawCount node.formula))
    (hscratch : d.stacks 30 = [])
    (hcount : total + rawCount node.formula ≤ 2 ^ n)
    (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    ∃ t ≤ 100 * (n + 1), ∃ e,
      Eval SparseDFSProgram.accumulate t d e ∧
      AfterVisit threshold ⟨rest, total + rawCount node.formula⟩ e ∧
      (∀ i, i ≠ 260 → i ≠ 263 → i ≠ 30 → e.stacks i = d.stacks i) ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled SparseDFSProgram.accumulate 256 256) prefixSteps
          (d.withPC (some (compiled SparseDFSProgram.accumulate 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (100 * (n + 1)) bound := by
  sorry

open SparseDFSProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end
