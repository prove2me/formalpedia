-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_Row_program_runs
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.program_runs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:52:15.082489+00:00
-- url     : https://prove2.me/theorems/fce47ad6-3042-43d6-b13e-6e94f1bcdf4e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.program_runs: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.program_runs` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramInterpreter.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramInterpreter.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram`):
--
--   ```lean
--   theorem program_runs (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
--       (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
--       (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
--       (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
--       (ht : high 6 = Squarefree.Program.lookupRecords entries)
--       (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
--       (ws : List (WeightedClause n (baseWidth p t) d)) :
--       let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
--         (List.replicate u true) (List.replicate J true)
--       let update := value p t M cache table minusOne one incidence u J
--       let input := Encoding.encodeList id (ws.map payload)
--       ∃ rr, RunsIn Native.program
--         (7+DynamicFold.work payload update (cost p t M cache table minusOne one incidence degree u J entries) ws [])
--         ((RecordPrograms.state rowPorts (base regs e high []) false true false input []).withPC
--           (some Native.program.entry))
--         ((RecordPrograms.state rowPorts
--           (base rr e high (Product.bytes (DynamicFold.value update ws []))) false true false [] []).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold.work` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Store` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.state` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.lookupRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.idle` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowPorts` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.program` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.base` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTriple.tableEncoding` (definitions bundle `OAIQ081S101` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.payload` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.value` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramInterpreter.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.program_runs)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (degree : List Bool) (u J : ℕ) (entries : List (List Bool × List Bool))

theorem program_runs (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
    (ws : List (WeightedClause n (baseWidth p t) d)) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    let update := value p t M cache table minusOne one incidence u J
    let input := Encoding.encodeList id (ws.map payload)
    ∃ rr, RunsIn Native.program
      (7+DynamicFold.work payload update (cost p t M cache table minusOne one incidence degree u J entries) ws [])
      ((RecordPrograms.state rowPorts (base regs e high []) false true false input []).withPC
        (some Native.program.entry))
      ((RecordPrograms.state rowPorts
        (base rr e high (Product.bytes (DynamicFold.value update ws []))) false true false [] []).withPC none) := by
  sorry

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row

end OAI.Algorithms
end
