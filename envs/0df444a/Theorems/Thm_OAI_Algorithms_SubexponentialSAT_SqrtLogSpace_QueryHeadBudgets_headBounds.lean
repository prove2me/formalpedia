-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryHeadBudgets_headBounds
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.headBounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:31:49.325598+00:00
-- url     : https://prove2.me/theorems/39659bee-d31f-4077-afb1-4e05992df08e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.headBounds: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.headBounds` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryHeadBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryHeadBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets`, with `open OAI BitProgram StructuredCalls SubexpSetupStorage SubexpLiftRing`, `open SqrtLog SqrtLog.LeafProgram SqrtLog.LeafHeadSetupProgram`, `open HeadSumBudgets FactorTableBudgets`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial`):
--
--   ```lean
--   theorem headBounds (s : Native.Inputs) {d : ℕ} (q : Factor.Spec s.r s.Q s.n d)
--       (a : Data) (A L M width : ℕ) (ha : Native.Ready s a) (hbound : WordBound A a)
--       (hL : L ≤ A) (hM : M ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A)
--       (hu : q.u ≤ A) (hJ : q.J ≤ A) (hbit : q.bitWidth ≤ A)
--       (hwidth : width ≤ A) (hrows : ∀ f (hf : f < q.rows.length), q.rows[f].length ≤ A)
--       (hmark : q.markedClause.length ≤ A)
--       (hR : q.p.R = s.R) (hword : q.p.width = s.width) (hpower : q.p.power = s.power)
--       (hdimension : q.ps.length = s.D) (hradius : q.p.R+1 ≤ s.Q)
--       (hclauses : ∀ f (hf : f < q.rows.length),
--         ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
--           w.literals.length ≤ width) :
--       QueryVisitorHead.HeadBounds s q M (compact A) (source A) (arithmetic A)
--         (transient A) L width
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.arithmetic`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.compact` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.source` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.transient` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Ready` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.weightedRow` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.power` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.markedClause` (definitions bundle `OAIQ081S169` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.HeadBounds` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds.headBounds` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryHeadBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.headBounds)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
open OAI BitProgram StructuredCalls SubexpSetupStorage SubexpLiftRing
open SqrtLog SqrtLog.LeafProgram SqrtLog.LeafHeadSetupProgram
open HeadSumBudgets FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

theorem headBounds (s : Native.Inputs) {d : ℕ} (q : Factor.Spec s.r s.Q s.n d)
    (a : Data) (A L M width : ℕ) (ha : Native.Ready s a) (hbound : WordBound A a)
    (hL : L ≤ A) (hM : M ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A)
    (hu : q.u ≤ A) (hJ : q.J ≤ A) (hbit : q.bitWidth ≤ A)
    (hwidth : width ≤ A) (hrows : ∀ f (hf : f < q.rows.length), q.rows[f].length ≤ A)
    (hmark : q.markedClause.length ≤ A)
    (hR : q.p.R = s.R) (hword : q.p.width = s.width) (hpower : q.p.power = s.power)
    (hdimension : q.ps.length = s.D) (hradius : q.p.R+1 ≤ s.Q)
    (hclauses : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width) :
    QueryVisitorHead.HeadBounds s q M (compact A) (source A) (arithmetic A)
      (transient A) L width := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
end
