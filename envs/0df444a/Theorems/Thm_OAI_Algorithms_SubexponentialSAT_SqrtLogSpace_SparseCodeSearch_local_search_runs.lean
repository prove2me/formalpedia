-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SparseCodeSearch_local_search_runs
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.local_search_runs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:23:23.915622+00:00
-- url     : https://prove2.me/theorems/c8810c07-3746-4a4c-820a-32132101c2a1
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.local_search_runs: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.local_search_runs` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeSearch.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeSearch.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch`, with `open BitProgram StructuredCalls CodeCandidateProgram`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks`):
--
--   ```lean
--   theorem local_search_runs (t D d A : ℕ)
--       (hexists : ∃ Q : Fin t → Fin D → SparseCode.F3, SparseCode.HasDistance Q d)
--       (a : State 16 48) (ha : LocalMatrixReady t D d a)
--       (hab : ∀ i, (a.stacks i).length ≤ A) (hdim : a.stacks 46 = List.replicate (t * D) true)
--       (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
--       ∃ (n : ℕ) (out : State 16 48) (Q : Fin t → Fin D → SparseCode.F3), n ≤ localTime A t D d ∧
--         Eval localSearch n a out ∧ out.stacks 18 = matrixFrames Q ∧ SparseCode.HasDistance Q d ∧
--         LocalMatrixReady t D d out ∧ (∀ i, i ≠ 18 → out.stacks i = a.stacks i) ∧
--         (∀ i, (out.stacks i).length ≤ boundary A (t * D)) ∧
--         ∀ k c, k ≤ n → Trace (compiled localSearch 46 18) k
--           (a.withPC (some (compiled localSearch 46 18).entry)) c →
--           ∀ i, (c.stacks i).length ≤ localSpace A t D d
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.F3` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.boundary` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.localSpace` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.HasDistance` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.localTime` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.LocalMatrixReady` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.localSearch` (definitions bundle `OAIQ081S152` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.local_call` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeSearch.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.local_search_runs)

import Mathlib
import Definitions.Def_OAIQ081S152

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

open BitProgram StructuredCalls CodeCandidateProgram

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks

theorem local_search_runs (t D d A : ℕ)
    (hexists : ∃ Q : Fin t → Fin D → SparseCode.F3, SparseCode.HasDistance Q d)
    (a : State 16 48) (ha : LocalMatrixReady t D d a)
    (hab : ∀ i, (a.stacks i).length ≤ A) (hdim : a.stacks 46 = List.replicate (t * D) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (n : ℕ) (out : State 16 48) (Q : Fin t → Fin D → SparseCode.F3), n ≤ localTime A t D d ∧
      Eval localSearch n a out ∧ out.stacks 18 = matrixFrames Q ∧ SparseCode.HasDistance Q d ∧
      LocalMatrixReady t D d out ∧ (∀ i, i ≠ 18 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ boundary A (t * D)) ∧
      ∀ k c, k ≤ n → Trace (compiled localSearch 46 18) k
        (a.withPC (some (compiled localSearch 46 18).entry)) c →
        ∀ i, (c.stacks i).length ≤ localSpace A t D d := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
end
