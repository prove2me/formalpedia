-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CodeChecks_rejection_scan_runs_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.rejection_scan_runs_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:14:17.137345+00:00
-- url     : https://prove2.me/theorems/f7e681de-605f-48de-9163-1ffd83c68763
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.rejection_scan_runs_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.rejection_scan_runs_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks`, with `open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram`):
--
--   ```lean
--   theorem rejection_scan_runs_space {R S : ℕ} (p : CounterForPrograms.Ports R S)
--       (latch : Fin S) (hc : latch ≠ p.counter) (hs : latch ≠ p.scratch)
--       (body : Cmd R S) (dimension budget : ℕ) (reject : ℕ → Bool)
--       (a : State R S) (b : Bool)
--       (hbody : RejectionBody p latch body dimension budget a reject)
--       (hcounter : a.stacks p.counter =
--         Encoding.encodeList id (List.replicate dimension [false, false]))
--       (hscratch : a.stacks p.scratch = []) (hlatch : a.stacks latch = [b])
--       (B : ℕ) (hB : 1 ≤ B) (ha : ∀ i, (a.stacks i).length ≤ B) :
--       ∃ n out, n ≤ 4 ^ dimension * (budget + 42 * dimension + 12) + 3 ∧
--         Trace (ExecCNFTupleEnumeration.program p body) n
--           (a.withPC (some (ExecCNFTupleEnumeration.program p body).entry)) (out.withPC none) ∧
--         RejectionFrame p latch a out ∧ out.stacks p.scratch = [] ∧
--         out.stacks latch = [b || (List.range' 0 (4 ^ dimension)).any reject] ∧
--         (∀ prefixSteps intermediate, prefixSteps ≤ n →
--           Trace (ExecCNFTupleEnumeration.program p body) prefixSteps
--             (a.withPC (some (ExecCNFTupleEnumeration.program p body).entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length ≤
--             max (B + budget) (S * B + 7 * (6 * dimension + 1) + 4))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.Ports` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.enumerate` and `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.program` (definitions bundle `OAIQ081S082` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.RejectionBody` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.RejectionFrame` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.rejection_scan_runs_space)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S114

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem rejection_scan_runs_space {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (latch : Fin S) (hc : latch ≠ p.counter) (hs : latch ≠ p.scratch)
    (body : Cmd R S) (dimension budget : ℕ) (reject : ℕ → Bool)
    (a : State R S) (b : Bool)
    (hbody : RejectionBody p latch body dimension budget a reject)
    (hcounter : a.stacks p.counter =
      Encoding.encodeList id (List.replicate dimension [false, false]))
    (hscratch : a.stacks p.scratch = []) (hlatch : a.stacks latch = [b])
    (B : ℕ) (hB : 1 ≤ B) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ n out, n ≤ 4 ^ dimension * (budget + 42 * dimension + 12) + 3 ∧
      Trace (ExecCNFTupleEnumeration.program p body) n
        (a.withPC (some (ExecCNFTupleEnumeration.program p body).entry)) (out.withPC none) ∧
      RejectionFrame p latch a out ∧ out.stacks p.scratch = [] ∧
      out.stacks latch = [b || (List.range' 0 (4 ^ dimension)).any reject] ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (ExecCNFTupleEnumeration.program p body) prefixSteps
          (a.withPC (some (ExecCNFTupleEnumeration.program p body).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          max (B + budget) (S * B + 7 * (6 * dimension + 1) + 4)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end
