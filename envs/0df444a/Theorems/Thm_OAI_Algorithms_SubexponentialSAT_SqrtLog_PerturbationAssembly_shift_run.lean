-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_shift_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift_run
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:08:33.972825+00:00
-- url     : https://prove2.me/theorems/008ec87f-bca7-4567-a281-cd25aca8bd66
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyShift.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyShift.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl`, `open PerturbationProgram`, `open CRTLocalProgram (ServiceSpec LowFrame serviceSpec_frame)`):
--
--   ```lean
--   theorem shift_run {C A : Type*} (s : Store) (encC : C → List Bool)
--       (encA : A → List Bool) (lift : C → A) (multiply add : Code)
--       (mulOp addOp : A → A → A) (Km Ka J W : ℕ)
--       (hm : ServiceSpec s encA multiply mulOp Km)
--       (ha : ServiceSpec s encA add addOp Ka)
--       (hc : ∀ c, (encC c).length=W) (hw : ∀ a, (encA a).length=J*W)
--       (hlift : ∀ c, Padding.cell J W (encC c)=encA (lift c))
--       (P : List C) (x zero : A)
--       (hrow : s 219=HornerProgram.encodePolynomial encC P)
--       (hcount : (s 210).length=P.length) (hwidth : (s 211).length=W)
--       (hx : s 247=encA x) (hz : s 192=encA zero)
--       (hJ : s 243=List.replicate J true)
--       (hzero : s 104=List.replicate W false)
--       (h254 : s 254=List.replicate W false)
--       (he : ∀ i ∈ shiftScratch, s i=[]) :
--       ExecutesIn (shift multiply add) (shiftBudget P.length J W Km Ka) s
--         (Function.update (Function.update s 219 []) 240
--           (encA (HornerProgram.fold (HornerProgram.stepValue mulOp addOp x)
--             (P.map lift).reverse zero)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.encodePolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.fold` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.stepValue` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shiftScratch` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Code` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shiftBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Padding.cell` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.ExecutesIn` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.ServiceSpec` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift` (definitions bundle `OAIQ081S150` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_shift_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationAssemblyShift.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift_run)

import Mathlib
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
open PerturbationProgram
open CRTLocalProgram (ServiceSpec LowFrame serviceSpec_frame)

theorem shift_run {C A : Type*} (s : Store) (encC : C → List Bool)
    (encA : A → List Bool) (lift : C → A) (multiply add : Code)
    (mulOp addOp : A → A → A) (Km Ka J W : ℕ)
    (hm : ServiceSpec s encA multiply mulOp Km)
    (ha : ServiceSpec s encA add addOp Ka)
    (hc : ∀ c, (encC c).length=W) (hw : ∀ a, (encA a).length=J*W)
    (hlift : ∀ c, Padding.cell J W (encC c)=encA (lift c))
    (P : List C) (x zero : A)
    (hrow : s 219=HornerProgram.encodePolynomial encC P)
    (hcount : (s 210).length=P.length) (hwidth : (s 211).length=W)
    (hx : s 247=encA x) (hz : s 192=encA zero)
    (hJ : s 243=List.replicate J true)
    (hzero : s 104=List.replicate W false)
    (h254 : s 254=List.replicate W false)
    (he : ∀ i ∈ shiftScratch, s i=[]) :
    ExecutesIn (shift multiply add) (shiftBudget P.length J W Km Ka) s
      (Function.update (Function.update s 219 []) 240
        (encA (HornerProgram.fold (HornerProgram.stepValue mulOp addOp x)
          (P.map lift).reverse zero))) := by
  sorry

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end
