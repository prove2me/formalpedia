-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_add_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.add_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:56:47.708636+00:00
-- url     : https://prove2.me/theorems/2d0a01ca-cfb5-41e1-9502-7155d613e8c0
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.add_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.add_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramAdd.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramAdd.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram`, with `open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open HashCircuitProgram.Native`, `open MomentsProgram`):
--
--   ```lean
--   theorem add_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
--       (cache : RingProgram.ScalarCache p t)
--       {K : Type*} [DecidableEq K] {d : ℕ}
--       (key : K → List Bool) (hk : Function.Injective key)
--       (table : List Bool) (degree width uCap zCap : List Bool)
--       (hd : degree.length=d) (hw : width.length=baseWidth p t)
--       (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
--       (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
--       (ha : high 11=Normalize.bytes key source)
--       (hb : high 5=Normalize.bytes key seed) (htmp : high 14=[]) :
--       let e:=Product.idle M.bits width cache.zero.val table degree uCap zCap
--       let result:=Normalize.bytes key (Normalize.run p t M cache source seed)
--       ∃ cost ≤ 18*(Normalize.bytes key source).length+9*(Normalize.bytes key seed).length+
--         9*result.length+9*degree.length+Normalize.work p t M cache key source seed+43,
--         ∃ rr, Eval add cost (Memory.state regs (Product.tapes e) high)
--           (Memory.state rr (Product.tapes e) (binaryResult high result))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Store` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.tapes` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.binaryResult` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.idle` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory.state` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.add` (definitions bundle `OAIQ081S102` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.run` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.work` (definitions bundle `OAIQ081S139` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.arithmetic_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.accumulator_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.add_constant_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramAdd.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.add_eval)

import Mathlib
import Definitions.Def_OAIQ081S139

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

theorem add_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    {K : Type*} [DecidableEq K] {d : ℕ}
    (key : K → List Bool) (hk : Function.Injective key)
    (table : List Bool) (degree width uCap zCap : List Bool)
    (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ha : high 11=Normalize.bytes key source)
    (hb : high 5=Normalize.bytes key seed) (htmp : high 14=[]) :
    let e:=Product.idle M.bits width cache.zero.val table degree uCap zCap
    let result:=Normalize.bytes key (Normalize.run p t M cache source seed)
    ∃ cost ≤ 18*(Normalize.bytes key source).length+9*(Normalize.bytes key seed).length+
      9*result.length+9*degree.length+Normalize.work p t M cache key source seed+43,
      ∃ rr, Eval add cost (Memory.state regs (Product.tapes e) high)
        (Memory.state rr (Product.tapes e) (binaryResult high result)) := by
  sorry

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end
