-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SparseCodeSearch_core_runs
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core_runs
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:50:11.523393+00:00
-- url     : https://prove2.me/theorems/13e461d2-0e06-4ffa-ae10-51f76f5a8234
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core_runs: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core_runs` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeSearch.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeSearch.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch`, with `open BitProgram StructuredCalls CodeCandidateProgram`):
--
--   ```lean
--   theorem core_runs (candidate : Cmd 16 48) (matrix : Fin 48)
--       (hm40 : matrix ≠ 40) (hm41 : matrix ≠ 41) (hm42 : matrix ≠ 42) (hm45 : matrix ≠ 45)
--       (Ready : State 16 48 → Prop) (Good : List Bool → Prop)
--       (hready : ∀ a b, Ready a →
--         (∀ i, i ≠ matrix → i ≠ 40 → i ≠ 41 → i ≠ 42 → b.stacks i = a.stacks i) → Ready b)
--       (hcopy : ∀ a, Ready a → a.stacks 45 = [])
--       (d B T C : ℕ) (hcap : 6 * d + 1 ≤ B)
--       (hchecks : ∀ (words : List (List Bool)) (a : State 16 48),
--         words.map List.length = List.replicate d 2 → Ready a →
--         (∀ i, (a.stacks i).length ≤ B) → a.stacks 40 = Encoding.encodeList id words →
--         ∃ n b, n ≤ T ∧ Eval candidate n a b ∧
--           (∀ i, i ≠ matrix → b.stacks i = a.stacks i) ∧
--           (∀ i, (b.stacks i).length ≤ B) ∧
--           (b.regs 15 = true → Good (b.stacks matrix)) ∧
--           ∀ k c, k ≤ n → Trace (compiled candidate 40 42) k
--             (a.withPC (some (compiled candidate 40 42).entry)) c →
--             ∀ i, (c.stacks i).length ≤ C)
--       (target : List (List Bool)) (htarget : target.map List.length = List.replicate d 2)
--       (haccept : ∀ a, Ready a → (∀ i, (a.stacks i).length ≤ B) →
--         a.stacks 40 = Encoding.encodeList id target →
--         ∃ n b, Eval candidate n a b ∧ b.regs 15 = true)
--       (base a : State 16 48) (ha : Invariant matrix Ready Good base B a)
--       (hc : a.stacks 40 = Encoding.encodeList id (List.replicate d [false, false]))
--       (hs : a.stacks 41 = []) :
--       ∃ n out, n ≤ 4 ^ d * (T + 7 * (B + C) + 10 + 42 * d + 12) + 3 ∧
--         Trace (core candidate) n (a.withPC (some (core candidate).entry)) (out.withPC none) ∧
--         Invariant matrix Ready Good base B out ∧ out.stacks 41 = [] ∧
--         out.stacks 40 = Encoding.encodeList id (List.replicate d [false, false]) ∧
--         out.stacks 42 ≠ [] ∧ Good (out.stacks matrix) ∧
--         ∀ k c, k ≤ n → Trace (core candidate) k
--           (a.withPC (some (core candidate).entry)) c →
--           ∀ i, (c.stacks i).length ≤
--             max (56 * (B + C) + 10) (48 * B + 7 * (6 * d + 1) + 4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.enumerate` (definitions bundle `OAIQ081S082` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.counterPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.selection` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.Invariant` (definitions bundle `OAIQ081S137` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graph_search_runs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.local_search_runs` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeSearch.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core_runs)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S137

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

open BitProgram StructuredCalls CodeCandidateProgram

theorem core_runs (candidate : Cmd 16 48) (matrix : Fin 48)
    (hm40 : matrix ≠ 40) (hm41 : matrix ≠ 41) (hm42 : matrix ≠ 42) (hm45 : matrix ≠ 45)
    (Ready : State 16 48 → Prop) (Good : List Bool → Prop)
    (hready : ∀ a b, Ready a →
      (∀ i, i ≠ matrix → i ≠ 40 → i ≠ 41 → i ≠ 42 → b.stacks i = a.stacks i) → Ready b)
    (hcopy : ∀ a, Ready a → a.stacks 45 = [])
    (d B T C : ℕ) (hcap : 6 * d + 1 ≤ B)
    (hchecks : ∀ (words : List (List Bool)) (a : State 16 48),
      words.map List.length = List.replicate d 2 → Ready a →
      (∀ i, (a.stacks i).length ≤ B) → a.stacks 40 = Encoding.encodeList id words →
      ∃ n b, n ≤ T ∧ Eval candidate n a b ∧
        (∀ i, i ≠ matrix → b.stacks i = a.stacks i) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        (b.regs 15 = true → Good (b.stacks matrix)) ∧
        ∀ k c, k ≤ n → Trace (compiled candidate 40 42) k
          (a.withPC (some (compiled candidate 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ C)
    (target : List (List Bool)) (htarget : target.map List.length = List.replicate d 2)
    (haccept : ∀ a, Ready a → (∀ i, (a.stacks i).length ≤ B) →
      a.stacks 40 = Encoding.encodeList id target →
      ∃ n b, Eval candidate n a b ∧ b.regs 15 = true)
    (base a : State 16 48) (ha : Invariant matrix Ready Good base B a)
    (hc : a.stacks 40 = Encoding.encodeList id (List.replicate d [false, false]))
    (hs : a.stacks 41 = []) :
    ∃ n out, n ≤ 4 ^ d * (T + 7 * (B + C) + 10 + 42 * d + 12) + 3 ∧
      Trace (core candidate) n (a.withPC (some (core candidate).entry)) (out.withPC none) ∧
      Invariant matrix Ready Good base B out ∧ out.stacks 41 = [] ∧
      out.stacks 40 = Encoding.encodeList id (List.replicate d [false, false]) ∧
      out.stacks 42 ≠ [] ∧ Good (out.stacks matrix) ∧
      ∀ k c, k ≤ n → Trace (core candidate) k
        (a.withPC (some (core candidate).entry)) c →
        ∀ i, (c.stacks i).length ≤
          max (56 * (B + C) + 10) (48 * B + 7 * (6 * d + 1) + 4) := by
  sorry

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
end
