-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Middle_iteration_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.iteration_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:11:11.92695+00:00
-- url     : https://prove2.me/theorems/1b332d34-a28d-4e93-8133-04a03c657315
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.iteration_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.iteration_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramIteration.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramIteration.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram`, `open Polynomial`, `open CRTLocalProgram (ServiceSpec)`):
--
--   ```lean
--   theorem iteration_run {C A : Type*} [CommRing A] {Q : ℕ}
--       (encode : C → List Bool) (decode : C → A)
--       (localCode multiply add : Cmd 16 256) (mulOp addOp : C → C → C)
--       (Km Ka Kl W J : ℕ) (d : Data)
--       (nodes : Fin Q → C) (remaining processed : List (Fin Q)) (i : Fin Q)
--       (hfull : List.finRange Q = processed.reverse ++ i :: remaining)
--       (unit minusOne zero acc : C)
--       (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
--       (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
--       (hmd : ∀ a b, decode (mulOp a b) = decode a * decode b)
--       (had : ∀ a b, decode (addOp a b) = decode a + decode b)
--       (hunit : decode unit = 1) (hminus : decode minusOne = -1) (hzero : decode zero = 0)
--       (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
--       (hr : d.stacks 257 = (remaining.map nodes).flatMap encode)
--       (hp : d.stacks 258 = (processed.map nodes).flatMap encode)
--       (hu : d.stacks 207 = encode unit) (hn : d.stacks 211 = encode minusOne)
--       (hz : d.stacks 104 = encode zero) (hx : d.stacks 259 = encode (nodes i))
--       (hacc : d.stacks 261 = encode acc) (hJ : d.stacks 243 = List.replicate J true)
--       (h277 : (d.stacks 277).length = J * W)
--       (hc : ∀ j ∈ cleanPorts, d.stacks j = [])
--       (correction : List C) (hcl : correction.length = J) (H : A[X])
--       (hdenote : PolynomialAlgorithm.denote (correction.map decode) = H)
--       (hlocal : SubexpConvolutionControl.ExecutesIn localCode Kl
--         ((Local.prepared d).stacks ∘ localPorts)
--         (Function.update ((Local.prepared d).stacks ∘ localPorts) 244
--           (HornerProgram.encodePolynomial encode correction))) :
--       ∃ n ≤ budget Q J W Km Ka Kl, ∃ rf b,
--         Eval (command localCode multiply add) n d
--           ⟨rf, Function.update d.stacks 261 (encode b)⟩ ∧
--         decode b = decode acc + (JetCRT.cofactor (decode ∘ nodes) J i).eval 0 *
--           H.eval (-decode (nodes i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.JetCRT.cofactor` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm.denote` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.encodePolynomial` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.localPorts` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.cleanPorts` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.budget` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.ServiceSpec` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram.Data` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Local.prepared` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.command` (definitions bundle `OAIQ081S144` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ReconstructionProgramIteration.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.iteration_run)

import Mathlib
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open Polynomial
open CRTLocalProgram (ServiceSpec)

theorem iteration_run {C A : Type*} [CommRing A] {Q : ℕ}
    (encode : C → List Bool) (decode : C → A)
    (localCode multiply add : Cmd 16 256) (mulOp addOp : C → C → C)
    (Km Ka Kl W J : ℕ) (d : Data)
    (nodes : Fin Q → C) (remaining processed : List (Fin Q)) (i : Fin Q)
    (hfull : List.finRange Q = processed.reverse ++ i :: remaining)
    (unit minusOne zero acc : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
    (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
    (hmd : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (had : ∀ a b, decode (addOp a b) = decode a + decode b)
    (hunit : decode unit = 1) (hminus : decode minusOne = -1) (hzero : decode zero = 0)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (hr : d.stacks 257 = (remaining.map nodes).flatMap encode)
    (hp : d.stacks 258 = (processed.map nodes).flatMap encode)
    (hu : d.stacks 207 = encode unit) (hn : d.stacks 211 = encode minusOne)
    (hz : d.stacks 104 = encode zero) (hx : d.stacks 259 = encode (nodes i))
    (hacc : d.stacks 261 = encode acc) (hJ : d.stacks 243 = List.replicate J true)
    (h277 : (d.stacks 277).length = J * W)
    (hc : ∀ j ∈ cleanPorts, d.stacks j = [])
    (correction : List C) (hcl : correction.length = J) (H : A[X])
    (hdenote : PolynomialAlgorithm.denote (correction.map decode) = H)
    (hlocal : SubexpConvolutionControl.ExecutesIn localCode Kl
      ((Local.prepared d).stacks ∘ localPorts)
      (Function.update ((Local.prepared d).stacks ∘ localPorts) 244
        (HornerProgram.encodePolynomial encode correction))) :
    ∃ n ≤ budget Q J W Km Ka Kl, ∃ rf b,
      Eval (command localCode multiply add) n d
        ⟨rf, Function.update d.stacks 261 (encode b)⟩ ∧
      decode b = decode acc + (JetCRT.cofactor (decode ∘ nodes) J i).eval 0 *
        H.eval (-decode (nodes i)) := by
  sorry

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms
end
