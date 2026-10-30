-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CodeChecks_graph_stream_runs
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:14:05.492027+00:00
-- url     : https://prove2.me/theorems/831895f2-d5ca-415f-9973-d6c2f0c5900a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks`, with `open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram`):
--
--   ```lean
--   theorem graph_stream_runs {D r : ℕ} (s : Fin D → Cayley.Cube r)
--       (q : ℕ) (qbits Dbits : List Bool)
--       (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
--       (a : ScanState) (he : GraphWorkEmpty (projectState id graphStreamStacks a))
--       (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
--       (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits)
--       (hp : a.stacks 34 = []) (htmp : a.stacks 35 = []) (hcopy : a.stacks 39 = [])
--       (hcounter : a.stacks 36 = Encoding.encodeList id (List.replicate r [false, false]))
--       (hscratch : a.stacks 38 = []) (hlatch : a.stacks 37 = [false])
--       (B : ℕ) (hB : 1 ≤ B) (ha : ∀ i, (a.stacks i).length ≤ B) :
--       ∃ n out, n ≤ graphStreamBudget D r qbits.length Dbits.length ∧
--         Trace (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody) n
--           (a.withPC (some (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody).entry))
--           (out.withPC none) ∧ RejectionFrame graphCounterPorts 37 a out ∧ out.stacks 38 = [] ∧
--         (out.stacks 37 = [false] ↔ WalshExistence.Good q s) ∧
--         (∀ prefixSteps intermediate, prefixSteps ≤ n →
--           Trace (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody) prefixSteps
--             (a.withPC (some (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody).entry))
--             intermediate → ∀ i, (intermediate.stacks i).length ≤
--               max (B + graphCallbackBudget D r qbits.length Dbits.length + 68 * r + 24)
--                 (40 * B + 7 * (6 * r + 1) + 4))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackBudget` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graphStreamStacks` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.Good` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graphStreamBudget` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.enumerate` and `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.program` (definitions bundle `OAIQ081S082` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.ScanState` (definitions bundle `OAIQ081S098` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.GraphWorkEmpty` (definitions bundle `OAIQ081S102` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.RejectionFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graphCounterPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graphStreamBody` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_matrix_candidate_valid` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S102
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

theorem graph_stream_runs {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (a : ScanState) (he : GraphWorkEmpty (projectState id graphStreamStacks a))
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits)
    (hp : a.stacks 34 = []) (htmp : a.stacks 35 = []) (hcopy : a.stacks 39 = [])
    (hcounter : a.stacks 36 = Encoding.encodeList id (List.replicate r [false, false]))
    (hscratch : a.stacks 38 = []) (hlatch : a.stacks 37 = [false])
    (B : ℕ) (hB : 1 ≤ B) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ n out, n ≤ graphStreamBudget D r qbits.length Dbits.length ∧
      Trace (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody) n
        (a.withPC (some (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody).entry))
        (out.withPC none) ∧ RejectionFrame graphCounterPorts 37 a out ∧ out.stacks 38 = [] ∧
      (out.stacks 37 = [false] ↔ WalshExistence.Good q s) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody) prefixSteps
          (a.withPC (some (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤
            max (B + graphCallbackBudget D r qbits.length Dbits.length + 68 * r + 24)
              (40 * B + 7 * (6 * r + 1) + 4)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end
