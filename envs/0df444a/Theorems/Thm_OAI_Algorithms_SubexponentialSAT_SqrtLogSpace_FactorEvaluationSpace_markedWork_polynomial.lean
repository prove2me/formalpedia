-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorEvaluationSpace_markedWork_polynomial
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.markedWork_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:33:27.911132+00:00
-- url     : https://prove2.me/theorems/75a5b90d-9862-4ca0-a51d-e8354163bf56
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.markedWork_polynomial: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.markedWork_polynomial` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorEvaluationSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorEvaluationSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace`, with `open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open SqrtLog SqrtLog.LeafProgram`, `open HashCircuitProgram HashCircuitProgram.Native MomentsProgram`, `open IdempotentApplyProgram.Steps NativeSemantics FactorBounds`):
--
--   ```lean
--   theorem markedWork_polynomial (ctx : Context p t n d)
--       (minus : RingProgram.Code (Word (baseWidth p t)) d)
--       (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
--       (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
--       (ls : List (SAT.Literal (Fin n))) :
--       FactorServices.clauseBudget ctx minus one incidence (Cost.entries incidence) ls +
--         (2 * (Squarefree.Program.lookupRecords (Cost.entries incidence)).length + 3 +
--           Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
--             (FactorServices.clauseResult ctx minus one incidence ls)) ≤
--         serviceBudget (baseWidth p t) d n ctx.u ctx.J ls.length 0 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.serviceBudget` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.lookupRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.entries` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Raw` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.Good` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.productBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.clauseBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.clauseResult` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.markedFactor_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorEvaluationSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.markedWork_polynomial)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram
open HashCircuitProgram HashCircuitProgram.Native MomentsProgram
open IdempotentApplyProgram.Steps NativeSemantics FactorBounds

variable {p t n d : ℕ} [Fact p.Prime]

theorem markedWork_polynomial (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good ∅ ctx.u ctx.J one) (hseed : Good ∅ ctx.u ctx.J seed)
    (hi : ∀ v, Good ∅ ctx.u ctx.J (incidence v))
    (ls : List (SAT.Literal (Fin n))) :
    FactorServices.clauseBudget ctx minus one incidence (Cost.entries incidence) ls +
      (2 * (Squarefree.Program.lookupRecords (Cost.entries incidence)).length + 3 +
        Factor.productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (FactorServices.clauseResult ctx minus one incidence ls)) ≤
      serviceBudget (baseWidth p t) d n ctx.u ctx.J ls.length 0 0 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
end
