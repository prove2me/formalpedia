-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Factor_marked_value_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_value_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:28:34.288476+00:00
-- url     : https://prove2.me/theorems/ef1cf33e-1864-458c-84df-df035d682363
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_value_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_value_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramFactorValue.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramFactorValue.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open HashCircuitProgram HashCircuitProgram.Native`, `open IdempotentApplyProgram.Steps`, `open MomentsProgram`):
--
--   ```lean
--   theorem marked_value_eval (ctx : Context p t n d)
--       (minus : RingProgram.Code (Word (baseWidth p t)) d)
--       (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (entries : List (List Bool × List Bool))
--       (hl : ∀ v : Fin n,entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
--       (ls : List (SAT.Literal (Fin n))) (a : Data)
--       (hlow : ∀ i,a.stacks (Clause.callerStacks (Memory.lowPort i))=low ctx i)
--       (hsource : a.stacks 63=Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits))
--       (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
--       (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
--       (hwork : ∀ i ∈ FactorServices.clauseScratch,a.stacks (Clause.callerStacks i)=[])
--       (hseed : a.stacks 151=Product.bytes seed) (htmp : a.stacks 159=[]) :
--       let factor := FactorServices.clauseResult ctx minus one incidence ls
--       let result := Product.run p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor []
--       ∃ k b,k  ≤  FactorServices.clauseBudget ctx minus one incidence entries ls+
--           (2*(a.stacks 62).length+3+productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor) ∧
--         Eval (.seq Clause.caller (.seq (clear 62) accumulate)) k a b ∧
--         b.stacks=Function.update (Function.update (Function.update
--           (Function.update a.stacks 63 []) 67 []) 62 []) 151 (Product.bytes result)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory.lowPort` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Clause.callerStacks` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.clauseScratch` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.lookupRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.literalBits` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.clear` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Clause.caller`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.accumulate` (definitions bundle `OAIQ081S109` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.low` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.run` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.productBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.clauseBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.clauseResult` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.markedFactor_eval` and `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_marked_callback_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramFactorValue.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_value_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem marked_value_eval (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n,entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (ls : List (SAT.Literal (Fin n))) (a : Data)
    (hlow : ∀ i,a.stacks (Clause.callerStacks (Memory.lowPort i))=low ctx i)
    (hsource : a.stacks 63=Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits))
    (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
    (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
    (hwork : ∀ i ∈ FactorServices.clauseScratch,a.stacks (Clause.callerStacks i)=[])
    (hseed : a.stacks 151=Product.bytes seed) (htmp : a.stacks 159=[]) :
    let factor := FactorServices.clauseResult ctx minus one incidence ls
    let result := Product.run p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor []
    ∃ k b,k  ≤  FactorServices.clauseBudget ctx minus one incidence entries ls+
        (2*(a.stacks 62).length+3+productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor) ∧
      Eval (.seq Clause.caller (.seq (clear 62) accumulate)) k a b ∧
      b.stacks=Function.update (Function.update (Function.update
        (Function.update a.stacks 63 []) 67 []) 62 []) 151 (Product.bytes result) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end
