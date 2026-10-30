-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Native_middle_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:32:12.618102+00:00
-- url     : https://prove2.me/theorems/544f2c62-0503-434d-bbc9-c155fd8a5dd9
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramModelMiddle.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramModelMiddle.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram`, `open SubexpLiftRing SubexpQuarticRing`, `open DensePolynomialProgram`):
--
--   ```lean
--   theorem middle_run (t : ℕ) (ht : 0 < t) {d Q : ℕ} (hd : 0 < d)
--       (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
--       (cache : RingProgram.ScalarCache 3 t)
--       (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
--       (_hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
--       (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
--       (nodes : Fin Q → Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
--       (minusOne acc : Coeff t d)
--       (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
--       (processed remaining : List (Fin Q)) (i : Fin Q)
--       (hfull : List.finRange Q = processed.reverse ++ i :: remaining)
--       (input : SubexpCRTOuterProgram.Data)
--       (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
--         (input.stacks ∘ localPorts))
--       (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
--       (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
--         (input.stacks ∘ localPorts) scalarWidth frame)
--       (hbuffers : ∀ j, input.stacks (localPorts (SubexpConvolutionControl.bufferPorts j)) = [])
--       (hclean : ∀ j ∈ Middle.cleanPorts, input.stacks j = [])
--       (hlocalClean : ∀ j ∈ CRTLocalProgram.localWork, input.stacks (localPorts j) = [])
--       (hzero : input.stacks 104 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
--       (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
--       (hneg : input.stacks 211 = RingProgram.flat minusOne)
--       (hnode : input.stacks 213 = RingProgram.flat (nodes i))
--       (hnodes : input.stacks 214 = (List.ofFn nodes).flatMap RingProgram.flat)
--       (hindex : (input.stacks 216).length = i.val)
--       (hjet : input.stacks 225 = Fixed.encode (jets i))
--       (hJ : input.stacks 243 = List.replicate J true)
--       (hr : input.stacks 257 = (remaining.map nodes).flatMap RingProgram.flat)
--       (hp : input.stacks 258 = (processed.map nodes).flatMap RingProgram.flat)
--       (hx : input.stacks 259 = RingProgram.flat (nodes i))
--       (hacc : input.stacks 261 = RingProgram.flat acc)
--       (h277 : input.stacks 277 = DensePolynomialProgram.encode
--         (List.replicate J (RingProgram.modelProgram t a M cache).zeroRun.1))
--       (hexponent : (input.stacks 209).length = 3^d-2)
--       (hprecision : (input.stacks 212).length = t) :
--       ∃ n ≤ Middle.budget Q J (d*baseWidth 3 t)
--           (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
--           (HornerProgram.Services.addBudget (baseWidth 3 t) d)
--           (CRTLocalProgram.Native.budget Q i.val (3^d) t d J), ∃ rf b,
--         Eval middle n input ⟨rf, Function.update input.stacks 261 (RingProgram.flat b)⟩ ∧
--         (RingProgram.modelRing t ht hd a M cache).decode b =
--           (RingProgram.modelRing t ht hd a M cache).decode acc + term t ht hd a M cache nodes J jets i
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RingProgram` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree`, `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.Services.addBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.Services.mulBudget` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.bufferPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localWork` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.localPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.cleanPorts` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.budget` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.encode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.Poly` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.budget` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.Services.NativeReady` (definitions bundle `OAIQ081S116` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.modelTable` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.encode` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.term` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryCountReconstruction_run_space_of_outputs_with_full_frame` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramModelMiddle.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run)

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

theorem middle_run (t : ℕ) (ht : 0 < t) {d Q : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (_hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne acc : Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (processed remaining : List (Fin Q)) (i : Fin Q)
    (hfull : List.finRange Q = processed.reverse ++ i :: remaining)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (input.stacks ∘ localPorts))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (input.stacks ∘ localPorts) scalarWidth frame)
    (hbuffers : ∀ j, input.stacks (localPorts (SubexpConvolutionControl.bufferPorts j)) = [])
    (hclean : ∀ j ∈ Middle.cleanPorts, input.stacks j = [])
    (hlocalClean : ∀ j ∈ CRTLocalProgram.localWork, input.stacks (localPorts j) = [])
    (hzero : input.stacks 104 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hnode : input.stacks 213 = RingProgram.flat (nodes i))
    (hnodes : input.stacks 214 = (List.ofFn nodes).flatMap RingProgram.flat)
    (hindex : (input.stacks 216).length = i.val)
    (hjet : input.stacks 225 = Fixed.encode (jets i))
    (hJ : input.stacks 243 = List.replicate J true)
    (hr : input.stacks 257 = (remaining.map nodes).flatMap RingProgram.flat)
    (hp : input.stacks 258 = (processed.map nodes).flatMap RingProgram.flat)
    (hx : input.stacks 259 = RingProgram.flat (nodes i))
    (hacc : input.stacks 261 = RingProgram.flat acc)
    (h277 : input.stacks 277 = DensePolynomialProgram.encode
      (List.replicate J (RingProgram.modelProgram t a M cache).zeroRun.1))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t) :
    ∃ n ≤ Middle.budget Q J (d*baseWidth 3 t)
        (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
        (HornerProgram.Services.addBudget (baseWidth 3 t) d)
        (CRTLocalProgram.Native.budget Q i.val (3^d) t d J), ∃ rf b,
      Eval middle n input ⟨rf, Function.update input.stacks 261 (RingProgram.flat b)⟩ ∧
      (RingProgram.modelRing t ht hd a M cache).decode b =
        (RingProgram.modelRing t ht hd a M cache).decode acc + term t ht hd a M cache nodes J jets i := by
  sorry

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
end
