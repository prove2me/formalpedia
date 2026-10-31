-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableProgram_literalPayload_rel
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPayload_rel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:06:49.534614+00:00
-- url     : https://prove2.me/theorems/d927fb52-1b79-4742-a34b-2fa9f741e135
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPayload_rel: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPayload_rel` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram`, with `open OAI.Algorithms.SubexponentialSAT.SqrtLog`, `open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives`, `open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing`):
--
--   ```lean
--   theorem literalPayload_rel (s : OuterStore) (n W Klow Lrows Lpayload : ℕ) (Good : List Bool → Prop)
--       (hn : (s 552).length=n) (hm : (s 575).length=n)
--       (hzero : (s 547).length=W) (hone : (s 548).length=W)
--       (h545 : s 545=[]) (h557 : s 557=[]) (h220 : s 560=[])
--       (he : ∀ i∈originScratch,s (innerPort i)=[])
--       (hlow : (s 574).getD (s 573).length false=false →
--         ∀ regs : Fin 16 → Bool, ∃ words payload k rf,
--         k≤Klow ∧ words.length≤Lrows ∧ payload.length≤Lpayload ∧ Good payload ∧
--         Eval lowPayload k (⟨regs,s⟩ : OuterData)
--           (⟨rf,Function.update (Function.update s 545 words) 557 payload⟩ : OuterData))
--       (hhigh : (s 574).getD (s 573).length false=true →
--         Good (Encoding.frame (originKey n)++
--           Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)))
--       (hhighLength : (Encoding.frame (originKey n)++
--         Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)).length≤Lpayload)
--       (regs : Fin 16 → Bool) :
--       ∃ words payload k rf,
--         k≤10*(s 573).length+9*(s 574).length+18+
--           (10*(s 573).length+42*n+29*W+109)+Klow ∧
--         words.length≤Lrows ∧ payload.length≤Lpayload ∧ Good payload ∧
--         Eval literalPayload k (⟨regs,s⟩ : OuterData)
--           (⟨rf,Function.update (Function.update s 545 words) 557 payload⟩ : OuterData)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.originScratch` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.OuterStore` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.innerPort` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.originKey` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPayload` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.lowPayload` (definitions bundle `OAIQ081S189` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.native_literal` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPayload_rel)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem literalPayload_rel (s : OuterStore) (n W Klow Lrows Lpayload : ℕ) (Good : List Bool → Prop)
    (hn : (s 552).length=n) (hm : (s 575).length=n)
    (hzero : (s 547).length=W) (hone : (s 548).length=W)
    (h545 : s 545=[]) (h557 : s 557=[]) (h220 : s 560=[])
    (he : ∀ i∈originScratch,s (innerPort i)=[])
    (hlow : (s 574).getD (s 573).length false=false →
      ∀ regs : Fin 16 → Bool, ∃ words payload k rf,
      k≤Klow ∧ words.length≤Lrows ∧ payload.length≤Lpayload ∧ Good payload ∧
      Eval lowPayload k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update (Function.update s 545 words) 557 payload⟩ : OuterData))
    (hhigh : (s 574).getD (s 573).length false=true →
      Good (Encoding.frame (originKey n)++
        Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)))
    (hhighLength : (Encoding.frame (originKey n)++
      Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)).length≤Lpayload)
    (regs : Fin 16 → Bool) :
    ∃ words payload k rf,
      k≤10*(s 573).length+9*(s 574).length+18+
        (10*(s 573).length+42*n+29*W+109)+Klow ∧
      words.length≤Lrows ∧ payload.length≤Lpayload ∧ Good payload ∧
      Eval literalPayload k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update (Function.update s 545 words) 557 payload⟩ : OuterData) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end
