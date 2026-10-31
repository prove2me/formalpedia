-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashQueryParameterBounds_accepted_frontend_budget
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_frontend_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:55:59.280793+00:00
-- url     : https://prove2.me/theorems/1561b083-45b5-4372-b03a-59dc901c15f1
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_frontend_budget: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_frontend_budget` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryParameterBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryParameterBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds`, with `open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources`, `open HashGreedyCode HashQueryEntry ProducedQueryResources`):
--
--   ```lean
--   theorem accepted_frontend_budget :
--       ∃ C degree : ℕ, ∀ (n k B wordBound : ℕ) (F : RawCNF n)
--         (_hn : 0 < n) (hm : 0 < F.length)
--         (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
--         (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
--         ∀ d : State 40 896,
--         (∀ i ∈ ([782,783,784,785] : List (Fin 896)), (d.stacks i).length ≤ wordBound) →
--         d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
--         d.stacks 777 = HashGreedyProgram.encodedHistory
--           (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
--             (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) →
--         (d.stacks 783).length = HashCandidates.digitWidth F.length →
--         BinaryArithmetic.toNat (d.stacks 782) = F.length →
--         BinaryArithmetic.toNat (d.stacks 785) = n →
--         LeafProgram.Query.CleanWork (HighMarkedFrontend.project d) →
--         LeafScopeInputBounds.capacity (acceptedQuery F hm shifts Q rounds d) k ≤
--             106 * (HashQueryInputBounds.commonCap n F.length B wordBound + k) ^ 3 ∧
--           (acceptedQuery F hm shifts Q rounds d).inputBudget k ≤
--             C * (HashQueryInputBounds.commonCap n F.length B wordBound + k + 1) ^ degree
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates.digitWidth` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds.commonCap` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.clauseRecords` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.indexed` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.project` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.capacity` (definitions bundle `OAIQ081S110` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.encodedHistory` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.CleanWork` (definitions bundle `OAIQ081S127` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.acceptedQuery` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.inputBudget` (definitions bundle `OAIQ081S186` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.accepted_with_shadow` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HashQueryParameterBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_frontend_budget)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds

open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources
open HashGreedyCode HashQueryEntry ProducedQueryResources

theorem accepted_frontend_budget :
    ∃ C degree : ℕ, ∀ (n k B wordBound : ℕ) (F : RawCNF n)
      (_hn : 0 < n) (hm : 0 < F.length)
      (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
      (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ d : State 40 896,
      (∀ i ∈ ([782,783,784,785] : List (Fin 896)), (d.stacks i).length ≤ wordBound) →
      d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      d.stacks 777 = HashGreedyProgram.encodedHistory
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) →
      (d.stacks 783).length = HashCandidates.digitWidth F.length →
      BinaryArithmetic.toNat (d.stacks 782) = F.length →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      LeafProgram.Query.CleanWork (HighMarkedFrontend.project d) →
      LeafScopeInputBounds.capacity (acceptedQuery F hm shifts Q rounds d) k ≤
          106 * (HashQueryInputBounds.commonCap n F.length B wordBound + k) ^ 3 ∧
        (acceptedQuery F hm shifts Q rounds d).inputBudget k ≤
          C * (HashQueryInputBounds.commonCap n F.length B wordBound + k + 1) ^ degree := by
  sorry

open CostAssembly MulticolorTypes

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds
end
