-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CodeChecks_graph_matrix_candidate_valid
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_matrix_candidate_valid
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:42:46.224532+00:00
-- url     : https://prove2.me/theorems/3dafcc0e-cae7-4a22-a05a-cc02201bf354
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_matrix_candidate_valid: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_matrix_candidate_valid` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks`, with `open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram`):
--
--   ```lean
--   theorem graph_matrix_candidate_valid {D r : ℕ} (s : Fin D → Cayley.Cube r)
--       (q : ℕ) (qbits Dbits : List Bool)
--       (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
--       (xs : List (Bool × Bool))
--       (hfields : xs.map CodeCandidates.digitBits = CodeCandidates.matrixWords s)
--       (hvalid : xs.any (CodeCandidates.invalidDigit false) = false)
--       (a : MatrixState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A)
--       (he : ∀ i : Fin 29, a.stacks (Fin.castAdd 19 i) = [])
--       (ht : a.stacks 30 = List.replicate D true) (hq : a.stacks 31 = qbits) (hDbits : a.stacks 32 = Dbits)
--       (hr : a.stacks 33 = List.replicate r true)
--       (hp : a.stacks 34 = []) (htmp : a.stacks 35 = []) (hcounter : a.stacks 36 = [])
--       (hlatch : a.stacks 37 = []) (hscratch : a.stacks 38 = []) (hcopy : a.stacks 39 = [])
--       (hcurrent : a.stacks 40 = CodeCandidates.tupleBits xs)
--       (hinput : a.stacks 43 = []) (hpayload : a.stacks 44 = []) (houtertmp : a.stacks 45 = []) :
--       ∃ n out, n ≤ matrixCheckTime A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length)
--           (graphStreamBudget D r qbits.length Dbits.length) + 2 * A + 73 * (D * r) + 23 ∧
--         Eval graphMatrixCandidate n a out ∧
--         (out.regs 15 = true ↔ WalshExistence.Good q s) ∧
--         out.stacks = Function.update a.stacks 29 (matrixFrames s) ∧
--         (∀ k c, k ≤ n → Trace (compiled graphMatrixCandidate 40 42) k
--           (a.withPC (some (compiled graphMatrixCandidate 40 42).entry)) c →
--           ∀ i, (c.stacks i).length ≤ max (3 * A + 73 * (D * r) + 23)
--             (matrixCheckSpace A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates.digitBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates.invalidDigit`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.matrixCheckSpace` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.matrixCheckTime` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.Good` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graphStreamBudget` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates.matrixWords` (definitions bundle `OAIQ081S080` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.MatrixState` (definitions bundle `OAIQ081S098` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates.tupleBits` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graphMatrixCandidate` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graph_search_runs` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_matrix_candidate_valid)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem graph_matrix_candidate_valid {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (xs : List (Bool × Bool))
    (hfields : xs.map CodeCandidates.digitBits = CodeCandidates.matrixWords s)
    (hvalid : xs.any (CodeCandidates.invalidDigit false) = false)
    (a : MatrixState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A)
    (he : ∀ i : Fin 29, a.stacks (Fin.castAdd 19 i) = [])
    (ht : a.stacks 30 = List.replicate D true) (hq : a.stacks 31 = qbits) (hDbits : a.stacks 32 = Dbits)
    (hr : a.stacks 33 = List.replicate r true)
    (hp : a.stacks 34 = []) (htmp : a.stacks 35 = []) (hcounter : a.stacks 36 = [])
    (hlatch : a.stacks 37 = []) (hscratch : a.stacks 38 = []) (hcopy : a.stacks 39 = [])
    (hcurrent : a.stacks 40 = CodeCandidates.tupleBits xs)
    (hinput : a.stacks 43 = []) (hpayload : a.stacks 44 = []) (houtertmp : a.stacks 45 = []) :
    ∃ n out, n ≤ matrixCheckTime A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length)
        (graphStreamBudget D r qbits.length Dbits.length) + 2 * A + 73 * (D * r) + 23 ∧
      Eval graphMatrixCandidate n a out ∧
      (out.regs 15 = true ↔ WalshExistence.Good q s) ∧
      out.stacks = Function.update a.stacks 29 (matrixFrames s) ∧
      (∀ k c, k ≤ n → Trace (compiled graphMatrixCandidate 40 42) k
        (a.withPC (some (compiled graphMatrixCandidate 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (3 * A + 73 * (D * r) + 23)
          (matrixCheckSpace A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length))) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end
