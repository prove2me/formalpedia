-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_ReconstructionSpace_reconstruct_run_space
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:40:41.674753+00:00
-- url     : https://prove2.me/theorems/de6bca5a-d444-4e61-b1eb-a904de877f21
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/ReconstructionSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/ReconstructionSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace`, with `open OAI BitProgram StructuredCalls SubexpCRTOuterProgram`, `open SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open DensePolynomialProgram ReconstructionProgram.Native`):
--
--   ```lean
--   theorem reconstruct_run_space (t : ℕ) (ht : 0 < t) {d Q : ℕ} [NeZero Q] (hd : 0 < d)
--       (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
--       (cache : RingProgram.ScalarCache 3 t)
--       (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
--       (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
--       (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
--       (nodes : Fin Q → ReconstructionProgram.Native.Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
--       (minusOne : ReconstructionProgram.Native.Coeff t d)
--       (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
--       (input : SubexpCRTOuterProgram.Data)
--       (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
--         (ReconstructionProgram.NativeState.arithmeticBase input))
--       (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
--       (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
--         (ReconstructionProgram.NativeState.arithmeticBase input) scalarWidth frame)
--       (hclean : ∀ j ∈ ReconstructionProgram.NativeState.cleanPorts, input.stacks j = [])
--       (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
--       (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
--       (hneg : input.stacks 211 = RingProgram.flat minusOne)
--       (hJ : input.stacks 243 = List.replicate J true)
--       (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
--       (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
--       (hexponent : (input.stacks 209).length = 3^d-2)
--       (hprecision : (input.stacks 212).length = t)
--       (hdistinct : Function.Injective (fun i => a.rho t ht
--         ((RingProgram.modelRing t ht hd a M cache).decode (nodes i))))
--       (target : Polynomial (a.O t)) (hdegree : target.natDegree < Q*J)
--       (htargetJets : Reconstruction.HasJets (RingProgram.modelRing t ht hd a M cache)
--         nodes J (fun i => (jets i).1) target)
--       (S : ℕ) (hQsize : Q ≤ S) (hJsize : J ≤ S) (htsize : t ≤ S)
--       (hdsize : d ≤ S) (hqsize : 3^d ≤ S)
--       (hmodsize : (input.stacks 194).length ≤ S)
--       (hwidthsize : (input.stacks 202).length ≤ S)
--       (count m n : ℕ) (hcount : count ≤ m*2^n) (hlarge : m*2^n < 3^t)
--       (htarget : target.eval 0 = (count : a.O t)) :
--       ∃ (b : ReconstructionProgram.Native.Coeff t d) (rf : Fin 16 → Bool) (steps : ℕ),
--         steps ≤ 2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1 ∧
--         Trace ReconstructionProgram.Native.program steps (input.withPC (some ReconstructionProgram.Native.program.entry))
--           ((⟨rf, Function.update (ReconstructionProgram.Entry.prepared input.stacks) 261
--             (RingProgram.flat b)⟩ : Data).withPC none) ∧
--         (RingProgram.modelRing t ht hd a M cache).decode b = (count : a.O t) ∧
--         a.decodeCount t ht ((RingProgram.modelRing t ht hd a M cache).decode b) = count ∧
--         ∀ prefixSteps intermediate, prefixSteps ≤ steps →
--           Trace ReconstructionProgram.Native.program prefixSteps (input.withPC (some ReconstructionProgram.Native.program.entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length ≤
--             stackBits input.stacks + (2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.stackBits` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RingProgram` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree` and `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry.prepared` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.costConstant` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.residuePolynomial` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.E`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.rho` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState.cleanPorts` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction.HasJets` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.decodeCount` (definitions bundle `OAIQ081S080` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Model.Poly` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.Services.NativeReady` (definitions bundle `OAIQ081S116` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.modelTable` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.encode` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState.arithmeticBase` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.program` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.run_space` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/ReconstructionSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S158

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace

open OAI BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram ReconstructionProgram.Native

theorem reconstruct_run_space (t : ℕ) (ht : 0 < t) {d Q : ℕ} [NeZero Q] (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → ReconstructionProgram.Native.Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne : ReconstructionProgram.Native.Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (ReconstructionProgram.NativeState.arithmeticBase input))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (ReconstructionProgram.NativeState.arithmeticBase input) scalarWidth frame)
    (hclean : ∀ j ∈ ReconstructionProgram.NativeState.cleanPorts, input.stacks j = [])
    (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hJ : input.stacks 243 = List.replicate J true)
    (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
    (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t)
    (hdistinct : Function.Injective (fun i => a.rho t ht
      ((RingProgram.modelRing t ht hd a M cache).decode (nodes i))))
    (target : Polynomial (a.O t)) (hdegree : target.natDegree < Q*J)
    (htargetJets : Reconstruction.HasJets (RingProgram.modelRing t ht hd a M cache)
      nodes J (fun i => (jets i).1) target)
    (S : ℕ) (hQsize : Q ≤ S) (hJsize : J ≤ S) (htsize : t ≤ S)
    (hdsize : d ≤ S) (hqsize : 3^d ≤ S)
    (hmodsize : (input.stacks 194).length ≤ S)
    (hwidthsize : (input.stacks 202).length ≤ S)
    (count m n : ℕ) (hcount : count ≤ m*2^n) (hlarge : m*2^n < 3^t)
    (htarget : target.eval 0 = (count : a.O t)) :
    ∃ (b : ReconstructionProgram.Native.Coeff t d) (rf : Fin 16 → Bool) (steps : ℕ),
      steps ≤ 2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1 ∧
      Trace ReconstructionProgram.Native.program steps (input.withPC (some ReconstructionProgram.Native.program.entry))
        ((⟨rf, Function.update (ReconstructionProgram.Entry.prepared input.stacks) 261
          (RingProgram.flat b)⟩ : Data).withPC none) ∧
      (RingProgram.modelRing t ht hd a M cache).decode b = (count : a.O t) ∧
      a.decodeCount t ht ((RingProgram.modelRing t ht hd a M cache).decode b) = count ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace ReconstructionProgram.Native.program prefixSteps (input.withPC (some ReconstructionProgram.Native.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          stackBits input.stacks + (2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace
end
