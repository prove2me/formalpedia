-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_native_coordinate_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_coordinate_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:07:16.097457+00:00
-- url     : https://prove2.me/theorems/8d84a72b-40e8-499d-92bb-a02b89628370
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_coordinate_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_coordinate_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyNativeCoordinate.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyNativeCoordinate.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl`, `open DensePolynomialProgram`, `open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem native_coordinate_run (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       {d n : ℕ} (ops : RingProgram (Coeff (baseWidth p t) d))
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
--       (v : Fin n) (rest : List Bool)
--       (hrow : s 230=true::(Encoding.frame (HornerProgram.encodePolynomial RingProgram.flat P)++rest))
--       (hn : (s 212).length=n) (hv : (s 218).length=v.val)
--       (hcount : (s 210).length=P.length) (hwidth : (s 211).length=d*baseWidth p t)
--       (hx : s 247=Fixed.encode (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J))
--       (hJ : s 243=List.replicate J true) (h213 : s 213=List.replicate J true)
--       (h104 : s 104=List.replicate (d*baseWidth p t) false)
--       (h254 : s 254=List.replicate (d*baseWidth p t) false)
--       (heLoad : ∀ i ∈ coordinateLoadScratch,s i=[])
--       (heShift : ∀ i ∈ shiftScratch,s i=[])
--       (heEmit : ∀ i ∈ coordinateEmitScratch,s i=[]) :
--       ExecutesIn coordinate
--         (15*(P.length*(d*baseWidth p t))+11*n+17*v.val+38+
--           shiftBudget P.length J (d*baseWidth p t)
--             (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)+
--           PerturbationEmitProgram.budget J n (d*baseWidth p t)+2*n+5) s
--         (Function.update (Function.update (Function.update s 230 rest)
--           217 (coordinateResult ops J theta v P (s 217))) 218 (true::s 218))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RingProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.nativeMulBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.AddService.budget` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.bufferPorts` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.encodePolynomial` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.coordinateEmitScratch` (definitions bundle `OAIQ081S019` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.coordinateLoadScratch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shiftScratch` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.budget` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.addRun` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.mulRun` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shiftBudget` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.scalarProgram` (definitions bundle `OAIQ081S068` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.linear` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.zero` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.encode` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.coordinateResult` (definitions bundle `OAIQ081S135` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.coordinate` (definitions bundle `OAIQ081S150` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_scan_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyNativeCoordinate.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_coordinate_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S150

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem native_coordinate_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d n : ℕ} (ops : RingProgram (Coeff (baseWidth p t) d))
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
    (v : Fin n) (rest : List Bool)
    (hrow : s 230=true::(Encoding.frame (HornerProgram.encodePolynomial RingProgram.flat P)++rest))
    (hn : (s 212).length=n) (hv : (s 218).length=v.val)
    (hcount : (s 210).length=P.length) (hwidth : (s 211).length=d*baseWidth p t)
    (hx : s 247=Fixed.encode (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J))
    (hJ : s 243=List.replicate J true) (h213 : s 213=List.replicate J true)
    (h104 : s 104=List.replicate (d*baseWidth p t) false)
    (h254 : s 254=List.replicate (d*baseWidth p t) false)
    (heLoad : ∀ i ∈ coordinateLoadScratch,s i=[])
    (heShift : ∀ i ∈ shiftScratch,s i=[])
    (heEmit : ∀ i ∈ coordinateEmitScratch,s i=[]) :
    ExecutesIn coordinate
      (15*(P.length*(d*baseWidth p t))+11*n+17*v.val+38+
        shiftBudget P.length J (d*baseWidth p t)
          (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)+
        PerturbationEmitProgram.budget J n (d*baseWidth p t)+2*n+5) s
      (Function.update (Function.update (Function.update s 230 rest)
        217 (coordinateResult ops J theta v P (s 217))) 218 (true::s 218)) := by
  sorry

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end
