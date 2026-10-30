-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_WeightedCore_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:52:56.560378+00:00
-- url     : https://prove2.me/theorems/4c5a80a0-3956-41e0-abe6-412f7124e994
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramWeightedCore.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramWeightedCore.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram`):
--
--   ```lean
--   theorem command_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
--       (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
--       {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
--       (scalar : RingProgram.Code (Word (baseWidth p t)) d)
--       (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
--       (key : K → List Bool) (hk : Function.Injective key)
--       (entries seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
--       (regs : Fin 8 → Bool) (a : Product.Store)
--       (he : Product.scaleEnvironment a a.coeff = Squarefree.ScaleProgram.environment p t M cache table scalar degree width)
--       (hm : a.modulus = M.bits) (hwidth : a.width = width) (hdegree : a.degree = degree)
--       (hr : a.right = Squarefree.ScaleProgram.encode key entries)
--       (hseed : a.acc = Normalize.bytes key seed)
--       (hs : a.scaleSource = []) (hc : a.scalar = []) (ho : a.scaled = [])
--       (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
--       (h3 : a.keyZCap = []) (h4 : a.mapped = []) (h27 : a.normalSource = [])
--       (h51 : a.normalCount = []) :
--       let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
--       ∃ n ≤ 25*a.right.length+11*a.coeff.length+9*a.degree.length+
--         Squarefree.ScaleProgram.budget key entries + Normalize.work p t M cache key weighted seed+43,
--         ∃ rr, Eval command n (Product.state regs a)
--           (Product.state rr {a with coeff := [], acc := Normalize.bytes key (Normalize.run p t M cache weighted seed)})
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Store` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.Environment` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.scaleEnvironment` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.state` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.bytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.encode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.scaled` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.run` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.environment` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.work` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.accumulate_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.complement_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramWeightedCore.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S106
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S139

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable {K : Type*} [DecidableEq K]

theorem command_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (hk : Function.Injective key)
    (entries seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (a : Product.Store)
    (he : Product.scaleEnvironment a a.coeff = Squarefree.ScaleProgram.environment p t M cache table scalar degree width)
    (hm : a.modulus = M.bits) (hwidth : a.width = width) (hdegree : a.degree = degree)
    (hr : a.right = Squarefree.ScaleProgram.encode key entries)
    (hseed : a.acc = Normalize.bytes key seed)
    (hs : a.scaleSource = []) (hc : a.scalar = []) (ho : a.scaled = [])
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) (h27 : a.normalSource = [])
    (h51 : a.normalCount = []) :
    let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
    ∃ n ≤ 25*a.right.length+11*a.coeff.length+9*a.degree.length+
      Squarefree.ScaleProgram.budget key entries + Normalize.work p t M cache key weighted seed+43,
      ∃ rr, Eval command n (Product.state regs a)
        (Product.state rr {a with coeff := [], acc := Normalize.bytes key (Normalize.run p t M cache weighted seed)}) := by
  sorry

end SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore

end OAI.Algorithms
end
