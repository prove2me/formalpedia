-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorEvaluationSpace_indicatorBudget_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.indicatorBudget_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:33:26.154873+00:00
-- url     : https://prove2.me/theorems/39a05532-35a6-4606-8298-6e2215ebb57e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.indicatorBudget_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.indicatorBudget_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorEvaluationSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorEvaluationSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace`, with `open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open SqrtLog SqrtLog.LeafProgram`, `open HashCircuitProgram HashCircuitProgram.Native MomentsProgram`, `open IdempotentApplyProgram.Steps NativeSemantics FactorBounds`):
--
--   ```lean
--   theorem indicatorBudget_le (ctx : Context p t n d) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
--       (minus : RingProgram.Code (Word (baseWidth p t)) d)
--       (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (hone : Good (∅ : Finset (Fin n)) ctx.u ctx.J one)
--       (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v))
--       (ws : List (Row.WeightedClause n (baseWidth p t) d))
--       (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
--       (k : ℕ) (hk : ∀ w ∈ ws, w.literals.length ≤ k) :
--       FactorServices.indicatorBudget ctx minus one incidence (Cost.entries incidence) ws digits ≤
--         Cost.programBound (baseWidth p t) d n ctx.u ctx.J
--           (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J) k ws.length+
--         IdempotentApplyProgram.Bounds.totalEnvelope (baseWidth p t) d n ctx.u ctx.J
--           (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J) digits.length+4
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.programBound` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Triple` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.capacity` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.totalEnvelope` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.entries` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Raw` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.Good` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.indicatorBudget` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.hashWork_polynomial` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorEvaluationSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.indicatorBudget_le)

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

theorem indicatorBudget_le (ctx : Context p t n d) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hone : Good (∅ : Finset (Fin n)) ctx.u ctx.J one)
    (hi : ∀ v, Good (∅ : Finset (Fin n)) ctx.u ctx.J (incidence v))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (k : ℕ) (hk : ∀ w ∈ ws, w.literals.length ≤ k) :
    FactorServices.indicatorBudget ctx minus one incidence (Cost.entries incidence) ws digits ≤
      Cost.programBound (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J) k ws.length+
      IdempotentApplyProgram.Bounds.totalEnvelope (baseWidth p t) d n ctx.u ctx.J
        (IdempotentApplyProgram.Bounds.capacity ((∅ : Finset (Fin n)) : Finset (Fin n)) ctx.u ctx.J) digits.length+4 := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
end
