-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_Clause_callback_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.callback_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:51:31.940058+00:00
-- url     : https://prove2.me/theorems/aefbc5f9-c7d0-4be0-9d77-bcaffc1c4bc7
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.callback_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.callback_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramInterpreter.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramInterpreter.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram`):
--
--   ```lean
--   theorem callback_eval (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
--       (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
--       (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
--       (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
--       (ht : high 6 = Squarefree.Program.lookupRecords entries)
--       (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
--       (l : SAT.Literal (Fin n)) (acc : List (Product.Entry n (baseWidth p t) d)) (tail : List Bool) :
--       let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
--         (List.replicate u true) (List.replicate J true)
--       ∃ k ≤ cost p t M cache table minusOne one incidence degree u J entries l acc,
--         ∃ rr, Eval (literalStep arithmetic) k
--           (RecordPrograms.state literalPorts (base regs e high (Product.bytes acc))
--             false true false tail (literalBits l).reverse)
--           (RecordPrograms.state literalPorts
--             (base rr e high (Product.bytes (step p t M cache table minusOne one incidence u J l acc)))
--             false true false tail [])
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Store` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.state` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.lookupRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.idle` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.literalPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.literalStep` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.literalBits` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.arithmetic` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.base` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTriple.tableEncoding` (definitions bundle `OAIQ081S101` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.cost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.step` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.program_runs` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_value_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramInterpreter.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.callback_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause
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

theorem callback_eval (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
    (l : SAT.Literal (Fin n)) (acc : List (Product.Entry n (baseWidth p t) d)) (tail : List Bool) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    ∃ k ≤ cost p t M cache table minusOne one incidence degree u J entries l acc,
      ∃ rr, Eval (literalStep arithmetic) k
        (RecordPrograms.state literalPorts (base regs e high (Product.bytes acc))
          false true false tail (literalBits l).reverse)
        (RecordPrograms.state literalPorts
          (base rr e high (Product.bytes (step p t M cache table minusOne one incidence u J l acc)))
          false true false tail []) := by
  sorry

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause

end OAI.Algorithms
end
