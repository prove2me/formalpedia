-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_AssignmentSemantics_selectedFactor_good
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_good
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:27:15.171759+00:00
-- url     : https://prove2.me/theorems/70d57132-b87e-4d74-9d80-e9f781881b8a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_good: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_good` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramAssignmentSemanticsFactors.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramAssignmentSemanticsFactors.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics`, with `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open HashCircuitProgram HashCircuitProgram.Native`, `open NativeSemantics`, `open IdempotentApplyProgram.Steps (Context)`):
--
--   ```lean
--   theorem selectedFactor_good (ctx : Context p t n d) (vars : Finset (Fin n))
--       (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
--       (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
--       (hi : ∀ id v, Good vars ctx.u ctx.J (incidence id v))
--       (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
--       (marked : Bool) (clause : List (SAT.Literal (Fin n)))
--       (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
--       (id : ℕ) (factor : Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (h : selectedFactor ctx minus one incidence hashes marked clause digits id = some factor) :
--       Good vars ctx.u ctx.J factor
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Triple` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.Raw` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.Good` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.hash_step_value` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.marked_step_value` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramAssignmentSemanticsFactors.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_good)

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

namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open NativeSemantics
open IdempotentApplyProgram.Steps (Context)

variable {p t n d : ℕ} [Fact p.Prime]

theorem selectedFactor_good (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hone : Good vars ctx.u ctx.J one)
    (hi : ∀ id v, Good vars ctx.u ctx.J (incidence id v))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (id : ℕ) (factor : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (h : selectedFactor ctx minus one incidence hashes marked clause digits id = some factor) :
    Good vars ctx.u ctx.J factor := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
end
