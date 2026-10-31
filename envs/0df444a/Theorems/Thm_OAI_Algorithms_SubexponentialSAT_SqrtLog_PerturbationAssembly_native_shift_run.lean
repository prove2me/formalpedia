-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_native_shift_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_shift_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:06:50.57881+00:00
-- url     : https://prove2.me/theorems/ba3c03e0-42e5-434f-9020-558f2aadd36d
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_shift_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_shift_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyModel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyModel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl`, `open DensePolynomialProgram`, `open SubexponentialSAT.SubexpSymbolicCost`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem native_shift_run (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       {d : ℕ} (ops : RingProgram (Coeff (baseWidth p t) d))
--       (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
--       (hB : 0 < baseWidth p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
--       (hadd : ∀ a b, (ops.addRun a b).1 =
--         (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
--       (hmul : ∀ a b, (ops.mulRun a b).1 =
--         (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
--       (s : Store) (J : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
--       (H : PairSpec.BaseReady p t M cache table s scalarWidth frame)
--       (hempty : ∀ i, s (bufferPorts i)=[])
--       (h121 : s 121=[]) (h122 : s 122=[])
--       (hcache : s 192=Fixed.encode (CRTLocalProgram.Model.zero ops.zeroRun.1 J))
--       (hJcount : (s 193).length=J)
--       (hzero : RingProgram.flat ops.zeroRun.1=List.replicate (d*baseWidth p t) false)
--       (P : List (Coeff (baseWidth p t) d)) (theta : Coeff (baseWidth p t) d)
--       (hrow : s 219=HornerProgram.encodePolynomial RingProgram.flat P)
--       (hcount : (s 210).length=P.length) (hwidth : (s 211).length=d*baseWidth p t)
--       (hx : s 247=Fixed.encode (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J))
--       (hJ : s 243=List.replicate J true)
--       (h104 : s 104=List.replicate (d*baseWidth p t) false)
--       (h254 : s 254=List.replicate (d*baseWidth p t) false)
--       (he : ∀ i ∈ shiftScratch, s i=[]) :
--       ExecutesIn (shift Fixed.mulCommand AddService.command)
--         (shiftBudget P.length J (d*baseWidth p t)
--           (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)) s
--         (Function.update (Function.update s 219 []) 240
--           (Fixed.encode (shiftedValue ops J theta P)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RingProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.nativeMulBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.AddService.budget` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.bufferPorts` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.encodePolynomial` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shiftScratch` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.addRun` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.mulRun` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shiftBudget` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.AddService.command` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.scalarProgram` (definitions bundle `OAIQ081S068` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.linear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.zero` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mulCommand` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.encode` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shiftedValue` (definitions bundle `OAIQ081S135` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift` (definitions bundle `OAIQ081S150` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_coordinate_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyModel.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_shift_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S150

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem native_shift_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (hB : 0 < baseWidth p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (J : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table s scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i)=[])
    (h121 : s 121=[]) (h122 : s 122=[])
    (hcache : s 192=Fixed.encode (CRTLocalProgram.Model.zero ops.zeroRun.1 J))
    (hJcount : (s 193).length=J)
    (hzero : RingProgram.flat ops.zeroRun.1=List.replicate (d*baseWidth p t) false)
    (P : List (Coeff (baseWidth p t) d)) (theta : Coeff (baseWidth p t) d)
    (hrow : s 219=HornerProgram.encodePolynomial RingProgram.flat P)
    (hcount : (s 210).length=P.length) (hwidth : (s 211).length=d*baseWidth p t)
    (hx : s 247=Fixed.encode (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J))
    (hJ : s 243=List.replicate J true)
    (h104 : s 104=List.replicate (d*baseWidth p t) false)
    (h254 : s 254=List.replicate (d*baseWidth p t) false)
    (he : ∀ i ∈ shiftScratch, s i=[]) :
    ExecutesIn (shift Fixed.mulCommand AddService.command)
      (shiftBudget P.length J (d*baseWidth p t)
        (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)) s
      (Function.update (Function.update s 219 []) 240
        (Fixed.encode (shiftedValue ops J theta P))) := by
  sorry

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end
