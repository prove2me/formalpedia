-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryHeadBudgets_loader_caps
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.loader_caps
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:17:53.551676+00:00
-- url     : https://prove2.me/theorems/ed17a976-e14f-47eb-9e43-af285e14cefe
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.loader_caps: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.loader_caps` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryHeadBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryHeadBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets`, with `open OAI BitProgram StructuredCalls SubexpSetupStorage SubexpLiftRing`, `open SqrtLog SqrtLog.LeafProgram SqrtLog.LeafHeadSetupProgram`, `open HeadSumBudgets FactorTableBudgets`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial`):
--
--   ```lean
--   theorem loader_caps (s : Native.Inputs) (a : Data) (A L : ℕ)
--       (ha : Native.Ready s a) (hbound : WordBound A a) (hL : L ≤ A) :
--       SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L ≤ scalarCap A ∧
--       QueryVisitorLoadBounds.matrixEnvelope s L ≤ scalarCap A ∧
--       QueryVisitorLoadBounds.keyEnvelope s L ≤ scalarCap A ∧
--       11*s.n+6 ≤ scalarCap A
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.scalarCap` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.retainedOutputBound` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Ready` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.columnLength` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.keyEnvelope` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds.matrixEnvelope` (definitions bundle `OAIQ081S179` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.headBounds` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryHeadBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.loader_caps)

import Mathlib
import Definitions.Def_OAIQ081S179

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
open OAI BitProgram StructuredCalls SubexpSetupStorage SubexpLiftRing
open SqrtLog SqrtLog.LeafProgram SqrtLog.LeafHeadSetupProgram
open HeadSumBudgets FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

theorem loader_caps (s : Native.Inputs) (a : Data) (A L : ℕ)
    (ha : Native.Ready s a) (hbound : WordBound A a) (hL : L ≤ A) :
    SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L ≤ scalarCap A ∧
    QueryVisitorLoadBounds.matrixEnvelope s L ≤ scalarCap A ∧
    QueryVisitorLoadBounds.keyEnvelope s L ≤ scalarCap A ∧
    11*s.n+6 ≤ scalarCap A := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
end
