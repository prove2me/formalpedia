-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Indicator_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:29:39.799519+00:00
-- url     : https://prove2.me/theorems/06ff8957-9897-459d-9bea-7df775680714
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramIndicator.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramIndicator.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open HashCircuitProgram HashCircuitProgram.Native`, `open IdempotentApplyProgram.Steps`, `open MomentsProgram`):
--
--   ```lean
--   theorem command_eval {p t n d : ℕ} [Fact p.Prime] (ctx : Context p t n d)
--       (hd : 0 < d) (hB : 0 < baseWidth p t)
--       (minus : RingProgram.Code (Word (baseWidth p t)) d)
--       (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
--       (entries : List (List Bool × List Bool))
--       (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
--       (ws : List (Row.WeightedClause n (baseWidth p t) d))
--       (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
--       (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
--       (ht : high 6 = Squarefree.Program.lookupRecords entries)
--       (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minus)
--       (htape : high 22 = IdempotentApplyProgram.triplesTape digits)
--       (h23 : high 23 = []) (hshape : (high 32).length = n)
--       (hready : IdempotentApplyProgram.Multiplier.ready high) :
--       let e := Product.idle ctx.modulus.bits ctx.width ctx.cache.zero.val
--         (RingTriple.tableEncoding ctx.table) (List.replicate d true)
--         (List.replicate ctx.u true) (List.replicate ctx.J true)
--       ∃ k rr, k ≤ 7 + DynamicFold.work Row.payload
--           (Row.value p t ctx.modulus ctx.cache ctx.table minus one incidence ctx.u ctx.J)
--           (Row.cost p t ctx.modulus ctx.cache ctx.table minus one incidence
--             (List.replicate d true) ctx.u ctx.J entries) ws [] +
--           IdempotentApplyProgram.applicationBudget ctx minus (rawHash ctx minus one incidence ws) one digits ∧
--         Eval command k
--           (RecordPrograms.state rowPorts (Row.base regs e high []) false true false
--             (Encoding.encodeList id (ws.map Row.payload)) [])
--           (Memory.state rr (low ctx) (Function.update
--             (Row.recordHigh high (Product.bytes (rawHash ctx minus one incidence ws)) [] [])
--             11 (Product.bytes (result ctx minus one incidence ws digits))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold.work`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Store` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.recordHigh` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Triple` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.ready` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.state` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.lookupRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.idle` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowPorts` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory.state` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.base` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTriple.tableEncoding` (definitions bundle `OAIQ081S101` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.triplesTape` (definitions bundle `OAIQ081S103` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.applicationBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.low`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.payload` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.value` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.rawHash` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.result` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.hash_value_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramIndicator.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Indicator

attribute [local simp] Fin.addCases

open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

theorem command_eval {p t n d : ℕ} [Fact p.Prime] (ctx : Context p t n d)
    (hd : 0 < d) (hB : 0 < baseWidth p t)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minus)
    (htape : high 22 = IdempotentApplyProgram.triplesTape digits)
    (h23 : high 23 = []) (hshape : (high 32).length = n)
    (hready : IdempotentApplyProgram.Multiplier.ready high) :
    let e := Product.idle ctx.modulus.bits ctx.width ctx.cache.zero.val
      (RingTriple.tableEncoding ctx.table) (List.replicate d true)
      (List.replicate ctx.u true) (List.replicate ctx.J true)
    ∃ k rr, k ≤ 7 + DynamicFold.work Row.payload
        (Row.value p t ctx.modulus ctx.cache ctx.table minus one incidence ctx.u ctx.J)
        (Row.cost p t ctx.modulus ctx.cache ctx.table minus one incidence
          (List.replicate d true) ctx.u ctx.J entries) ws [] +
        IdempotentApplyProgram.applicationBudget ctx minus (rawHash ctx minus one incidence ws) one digits ∧
      Eval command k
        (RecordPrograms.state rowPorts (Row.base regs e high []) false true false
          (Encoding.encodeList id (ws.map Row.payload)) [])
        (Memory.state rr (low ctx) (Function.update
          (Row.recordHigh high (Product.bytes (rawHash ctx minus one incidence ws)) [] [])
          11 (Product.bytes (result ctx minus one incidence ws digits)))) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.Indicator

end OAI.Algorithms
end
