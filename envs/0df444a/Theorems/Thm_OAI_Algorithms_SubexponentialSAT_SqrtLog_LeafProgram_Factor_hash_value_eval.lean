-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Factor_hash_value_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.hash_value_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:28:06.814886+00:00
-- url     : https://prove2.me/theorems/4ef98ce2-7fd1-4dfc-8527-395c16aaef34
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.hash_value_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.hash_value_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramFactorValue.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramFactorValue.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open HashCircuitProgram HashCircuitProgram.Native`, `open IdempotentApplyProgram.Steps`, `open MomentsProgram`):
--
--   ```lean
--   theorem hash_value_eval (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
--       (minus : RingProgram.Code (Word (baseWidth p t)) d)
--       (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (entries : List (List Bool × List Bool))
--       (hl : ∀ v : Fin n,entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
--       (ws : List (Row.WeightedClause n (baseWidth p t) d))
--       (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
--       (a : Data)
--       (hlow : ∀ i,a.stacks (indicatorStacks (Memory.lowPort i))=low ctx i)
--       (hsource : a.stacks 64=Encoding.encodeList id (ws.map Row.payload))
--       (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
--       (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
--       (htape : a.stacks 143=IdempotentApplyProgram.triplesTape digits)
--       (hshape : (a.stacks 88).length=n)
--       (hwork : ∀ i ∈ FactorServices.indicatorScratch,a.stacks (indicatorStacks i)=[])
--       (hseed : a.stacks 151=Product.bytes seed) (htmp : a.stacks 159=[]) :
--       let factor := Indicator.result ctx minus one incidence ws digits
--       let result := Product.run p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor []
--       ∃ k b,k ≤ FactorServices.indicatorBudget ctx minus one incidence entries ws digits+
--           (2*(Product.bytes (Indicator.rawHash ctx minus one incidence ws)).length+
--             2*(a.stacks 62).length+6+productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor) ∧
--         Eval (.seq indicator (.seq (clear 68) (.seq (clear 62) accumulate))) k a b ∧
--         b.stacks=Function.update (Function.update (Function.update (Function.update
--           (Function.update a.stacks 64 []) 67 []) 68 []) 62 []) 151 (Product.bytes result)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory.lowPort` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Triple` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.indicatorStacks` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.indicatorScratch` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.lookupRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.clear` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.triplesTape` (definitions bundle `OAIQ081S103` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.accumulate` (definitions bundle `OAIQ081S109` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.low`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.payload` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.indicator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.productBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.indicatorBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.rawHash` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.result` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.expanded_hash_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramFactorValue.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.hash_value_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem hash_value_eval (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n,entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (a : Data)
    (hlow : ∀ i,a.stacks (indicatorStacks (Memory.lowPort i))=low ctx i)
    (hsource : a.stacks 64=Encoding.encodeList id (ws.map Row.payload))
    (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
    (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
    (htape : a.stacks 143=IdempotentApplyProgram.triplesTape digits)
    (hshape : (a.stacks 88).length=n)
    (hwork : ∀ i ∈ FactorServices.indicatorScratch,a.stacks (indicatorStacks i)=[])
    (hseed : a.stacks 151=Product.bytes seed) (htmp : a.stacks 159=[]) :
    let factor := Indicator.result ctx minus one incidence ws digits
    let result := Product.run p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor []
    ∃ k b,k ≤ FactorServices.indicatorBudget ctx minus one incidence entries ws digits+
        (2*(Product.bytes (Indicator.rawHash ctx minus one incidence ws)).length+
          2*(a.stacks 62).length+6+productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor) ∧
      Eval (.seq indicator (.seq (clear 68) (.seq (clear 62) accumulate))) k a b ∧
      b.stacks=Function.update (Function.update (Function.update (Function.update
        (Function.update a.stacks 64 []) 67 []) 68 []) 62 []) 151 (Product.bytes result) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end
