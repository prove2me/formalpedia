-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Native_command_value
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:32:02.321391+00:00
-- url     : https://prove2.me/theorems/f0edfd1d-1f38-4b9b-a14b-247f72b701f4
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramModel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramModel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram`, `open SubexpLiftRing SubexpQuarticRing`, `open DensePolynomialProgram`):
--
--   ```lean
--   theorem command_value (t : ℕ) (ht : 0 < t) {d Q : ℕ} (hd : 0 < d)
--       (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
--       (cache : RingProgram.ScalarCache 3 t)
--       (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
--       (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
--       (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
--       (nodes : Fin Q → Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
--       (minusOne : Coeff t d)
--       (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
--       (input : SubexpCRTOuterProgram.Data)
--       (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
--         (NativeState.arithmeticBase input))
--       (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
--       (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
--         (NativeState.arithmeticBase input) scalarWidth frame)
--       (hclean : ∀ j ∈ NativeState.cleanPorts, input.stacks j = [])
--       (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
--       (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
--       (hneg : input.stacks 211 = RingProgram.flat minusOne)
--       (hJ : input.stacks 243 = List.replicate J true)
--       (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
--       (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
--       (hexponent : (input.stacks 209).length = 3^d-2)
--       (hprecision : (input.stacks 212).length = t) :
--       let ops := RingProgram.modelRing t ht hd a M cache
--       let theta := fun i => ops.decode (nodes i)
--       ∃ n ≤ budget Q J t d (input.stacks 194).length (input.stacks 202).length,
--         ∃ (out : Data) (b : Coeff t d), Eval command n input out ∧
--         out.stacks = Function.update (Entry.prepared input.stacks) 261 (RingProgram.flat b) ∧
--         ops.decode b = SubexpCRTAtZero.value theta J (LocalValue.inverse theta (3^d) t J)
--           (fun i => CRTLocalProgram.Model.denote ops.decode (jets i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RingProgram` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry.prepared` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState.cleanPorts` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.inverse` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTAtZero.value` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.Poly` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.denote` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.Services.NativeReady` (definitions bundle `OAIQ081S116` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.modelTable` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.encode` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState.arithmeticBase` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.program_correct` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramModel.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S158

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram

theorem command_value (t : ℕ) (ht : 0 < t) {d Q : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne : Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (NativeState.arithmeticBase input))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (NativeState.arithmeticBase input) scalarWidth frame)
    (hclean : ∀ j ∈ NativeState.cleanPorts, input.stacks j = [])
    (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hJ : input.stacks 243 = List.replicate J true)
    (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
    (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t) :
    let ops := RingProgram.modelRing t ht hd a M cache
    let theta := fun i => ops.decode (nodes i)
    ∃ n ≤ budget Q J t d (input.stacks 194).length (input.stacks 202).length,
      ∃ (out : Data) (b : Coeff t d), Eval command n input out ∧
      out.stacks = Function.update (Entry.prepared input.stacks) 261 (RingProgram.flat b) ∧
      ops.decode b = SubexpCRTAtZero.value theta J (LocalValue.inverse theta (3^d) t J)
        (fun i => CRTLocalProgram.Model.denote ops.decode (jets i)) := by
  sorry

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
end
