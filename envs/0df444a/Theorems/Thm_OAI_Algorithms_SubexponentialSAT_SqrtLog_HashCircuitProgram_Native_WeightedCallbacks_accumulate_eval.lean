-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_WeightedCallbacks_accumulate_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.accumulate_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:52:26.354289+00:00
-- url     : https://prove2.me/theorems/a1b3a9f4-6f6c-4da0-90c0-cb189c1edf7a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.accumulate_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.accumulate_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramArithmeticNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramArithmeticNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram`, `open Memory`):
--
--   ```lean
--   theorem accumulate_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
--       (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
--       {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
--       (scalar : RingProgram.Code (Word (baseWidth p t)) d)
--       (degree width uCap zCap : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
--       (key : K → List Bool) (hk : Function.Injective key)
--       (entries seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
--       (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
--       (ha : high 11 = Squarefree.ScaleProgram.encode key entries)
--       (hc : high 9 = (RingProgram.flat scalar).reverse)
--       (hs : high 12 = Normalize.bytes key seed) (htmp : high 14 = []) :
--       let idle := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree uCap zCap
--       let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
--       let result := Normalize.bytes key (Normalize.run p t M cache weighted seed)
--       ∃ cost ≤ 36*(high 11).length+14*(high 9).length+9*(high 12).length+
--         9*result.length+9*degree.length+Squarefree.ScaleProgram.budget key entries+
--         Normalize.work p t M cache key weighted seed+74,
--         ∃ rr, Eval accumulate cost (Memory.state regs (Product.tapes idle) high)
--           (Memory.state rr (Product.tapes idle) (accumulatedHigh high result))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.tapes` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.accumulatedHigh` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.idle` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.accumulate` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory.state` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTriple.tableEncoding` (definitions bundle `OAIQ081S101` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.bytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.encode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.scaled` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.run` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.work` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.program_runs` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramArithmeticNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.accumulate_eval)

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

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open Memory

variable {K : Type*} [DecidableEq K]

theorem accumulate_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width uCap zCap : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (hk : Function.Injective key)
    (entries seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ha : high 11 = Squarefree.ScaleProgram.encode key entries)
    (hc : high 9 = (RingProgram.flat scalar).reverse)
    (hs : high 12 = Normalize.bytes key seed) (htmp : high 14 = []) :
    let idle := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree uCap zCap
    let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
    let result := Normalize.bytes key (Normalize.run p t M cache weighted seed)
    ∃ cost ≤ 36*(high 11).length+14*(high 9).length+9*(high 12).length+
      9*result.length+9*degree.length+Squarefree.ScaleProgram.budget key entries+
      Normalize.work p t M cache key weighted seed+74,
      ∃ rr, Eval accumulate cost (Memory.state regs (Product.tapes idle) high)
        (Memory.state rr (Product.tapes idle) (accumulatedHigh high result)) := by
  sorry

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks

end OAI.Algorithms
end
