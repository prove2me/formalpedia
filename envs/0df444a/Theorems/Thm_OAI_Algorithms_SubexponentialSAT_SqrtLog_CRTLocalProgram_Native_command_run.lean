-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_Native_command_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:22:54.285975+00:00
-- url     : https://prove2.me/theorems/61a020cc-ea2f-4e4b-8d8f-96b1344e5e4c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open DensePolynomialProgram`):
--
--   ```lean
--   theorem command_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
--       (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
--       (cache : RingProgram.ScalarCache 3 t)
--       (hcanon : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < 3^t)
--       (s : Store) (J q : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
--       (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) s)
--       (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
--       (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache) s scalarWidth frame)
--       (hbuffers : ∀ i, s (bufferPorts i) = [])
--       (minusOne theta : Coeff (baseWidth 3 t) d) (cs : List (Coeff (baseWidth 3 t) d))
--       (jet : Model.Poly (baseWidth 3 t) d J)
--       (hzero : s 104 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
--       (hone : s 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
--       (hminus : s 211 = RingProgram.flat minusOne) (htheta : s 213 = RingProgram.flat theta)
--       (hcs : s 214 = cs.flatMap RingProgram.flat) (hjet : s 225 = Fixed.encode jet)
--       (hJ : s 243 = List.replicate J true) (hJcache : (s 193).length = J)
--       (hzeroCache : s 192 = DensePolynomialProgram.encode
--         (List.replicate J (RingProgram.modelProgram t a M cache).zeroRun.1))
--       (hexponent : (s 209).length = q-2) (hprecision : (s 212).length = t)
--       (hclean : ∀ i ∈ localWork, s i = []) :
--       let ops := RingProgram.modelRing t ht hd a M cache
--       let factor := (cs.eraseIdx (s 216).length).foldl
--         (localUpdate (Model.scalarMul ops) (Model.scalarAdd ops) (Fixed.mul ops.program)
--           (fun c => Model.linear ops.zeroRun.1 ops.oneRun.1 c J) theta minusOne J)
--         (Model.constant ops.zeroRun.1 ops.oneRun.1 J)
--       ∃ (c : Coeff (baseWidth 3 t) d) (rest : List (Coeff (baseWidth 3 t) d)),
--         factor.1 = c :: rest ∧
--         ExecutesIn command (budget cs.length (s 216).length q t d J) s
--           (Function.update s 244 (Fixed.encode (Model.corrected ops minusOne c q t factor jet)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RingProgram` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.bufferPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localWork` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localUpdate` (definitions bundle `OAIQ081S028` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.encode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.constant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.corrected`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.linear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.scalarAdd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.scalarMul`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.Array` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mul` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.Services.NativeReady` (definitions bundle `OAIQ081S116` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.modelTable` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.encode` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CRTLocalProgramNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command_run)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open DensePolynomialProgram

theorem command_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (J q : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) s)
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache) s scalarWidth frame)
    (hbuffers : ∀ i, s (bufferPorts i) = [])
    (minusOne theta : Coeff (baseWidth 3 t) d) (cs : List (Coeff (baseWidth 3 t) d))
    (jet : Model.Poly (baseWidth 3 t) d J)
    (hzero : s 104 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : s 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hminus : s 211 = RingProgram.flat minusOne) (htheta : s 213 = RingProgram.flat theta)
    (hcs : s 214 = cs.flatMap RingProgram.flat) (hjet : s 225 = Fixed.encode jet)
    (hJ : s 243 = List.replicate J true) (hJcache : (s 193).length = J)
    (hzeroCache : s 192 = DensePolynomialProgram.encode
      (List.replicate J (RingProgram.modelProgram t a M cache).zeroRun.1))
    (hexponent : (s 209).length = q-2) (hprecision : (s 212).length = t)
    (hclean : ∀ i ∈ localWork, s i = []) :
    let ops := RingProgram.modelRing t ht hd a M cache
    let factor := (cs.eraseIdx (s 216).length).foldl
      (localUpdate (Model.scalarMul ops) (Model.scalarAdd ops) (Fixed.mul ops.program)
        (fun c => Model.linear ops.zeroRun.1 ops.oneRun.1 c J) theta minusOne J)
      (Model.constant ops.zeroRun.1 ops.oneRun.1 J)
    ∃ (c : Coeff (baseWidth 3 t) d) (rest : List (Coeff (baseWidth 3 t) d)),
      factor.1 = c :: rest ∧
      ExecutesIn command (budget cs.length (s 216).length q t d J) s
        (Function.update s 244 (Fixed.encode (Model.corrected ops minusOne c q t factor jet))) := by
  sorry

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Native

end OAI.Algorithms
end
