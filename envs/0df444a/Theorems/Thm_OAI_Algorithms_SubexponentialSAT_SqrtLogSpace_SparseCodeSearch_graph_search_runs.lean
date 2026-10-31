-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SparseCodeSearch_graph_search_runs
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graph_search_runs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:23:10.317304+00:00
-- url     : https://prove2.me/theorems/90238346-082a-43cf-8427-7a283f569425
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graph_search_runs: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graph_search_runs` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeSearch.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeSearch.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch`, with `open BitProgram StructuredCalls CodeCandidateProgram`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks`):
--
--   ```lean
--   theorem graph_search_runs (D r q A : ℕ) (qbits Dbits : List Bool)
--       (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
--       (hexists : ∃ Q : Fin D → Cayley.Cube r, WalshExistence.Good q Q)
--       (a : State 16 48) (ha : GraphMatrixReady D r qbits Dbits a)
--       (hab : ∀ i, (a.stacks i).length ≤ A) (hdim : a.stacks 46 = List.replicate (D * r) true)
--       (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
--       ∃ (n : ℕ) (out : State 16 48) (Q : Fin D → Cayley.Cube r), n ≤ graphTime A D r qbits.length Dbits.length ∧
--         Eval graphSearch n a out ∧ out.stacks 29 = matrixFrames Q ∧ WalshExistence.Good q Q ∧
--         GraphMatrixReady D r qbits Dbits out ∧ (∀ i, i ≠ 29 → out.stacks i = a.stacks i) ∧
--         (∀ i, (out.stacks i).length ≤ boundary A (D * r)) ∧
--         ∀ k c, k ≤ n → Trace (compiled graphSearch 46 29) k
--           (a.withPC (some (compiled graphSearch 46 29).entry)) c →
--           ∀ i, (c.stacks i).length ≤ graphSpace A D r qbits.length Dbits.length
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.boundary` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.Good` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graphSpace` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graphTime` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.GraphMatrixReady` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graphSearch` (definitions bundle `OAIQ081S152` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.graph_call` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeSearch.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graph_search_runs)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S152

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

open BitProgram StructuredCalls CodeCandidateProgram

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks

theorem graph_search_runs (D r q A : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (hexists : ∃ Q : Fin D → Cayley.Cube r, WalshExistence.Good q Q)
    (a : State 16 48) (ha : GraphMatrixReady D r qbits Dbits a)
    (hab : ∀ i, (a.stacks i).length ≤ A) (hdim : a.stacks 46 = List.replicate (D * r) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (n : ℕ) (out : State 16 48) (Q : Fin D → Cayley.Cube r), n ≤ graphTime A D r qbits.length Dbits.length ∧
      Eval graphSearch n a out ∧ out.stacks 29 = matrixFrames Q ∧ WalshExistence.Good q Q ∧
      GraphMatrixReady D r qbits Dbits out ∧ (∀ i, i ≠ 29 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ boundary A (D * r)) ∧
      ∀ k c, k ≤ n → Trace (compiled graphSearch 46 29) k
        (a.withPC (some (compiled graphSearch 46 29).entry)) c →
        ∀ i, (c.stacks i).length ≤ graphSpace A D r qbits.length Dbits.length := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
end
