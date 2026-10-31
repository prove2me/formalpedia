-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableNative_native_literal
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.native_literal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:06:27.918642+00:00
-- url     : https://prove2.me/theorems/d2d00512-6061-4da1-aa3b-52ba46557178
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.native_literal: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.native_literal` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative`, with `open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram`, `open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram`, `open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes`):
--
--   ```lean
--   theorem native_literal {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
--       (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
--       (u J n f S j : ℕ) (hu : 0 < u) (hJ : 0 < J)
--       (theta : Coeff (baseWidth 3 p.t) d)
--       (s : FactorTableProgram.OuterStore) (acc : List Bool)
--       (h : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
--         (FactorTableProgram.projectBase s) n)
--       (hsource : ∀ regs : Fin 16 → Bool, SourceReady.Input p ps P
--         (projectState id FactorTableProgram.basePort (sourceCallData s j acc regs)) j n f S)
--       (hj : j < n) (hn : n ≤ S) (hf : f ≤ S)
--       (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
--       (h545 : s 545 = []) (h555 : s 555 = []) (h557 : s 557 = [])
--       (hm : (s 575).length = n) (hmask : (s 857).length = n) (htmp : s 881 = [])
--       (regs : Fin 16 → Bool) :
--       ∃ payload k rf, k ≤ specializedLiteralWork p u J n S (s 574).length ∧
--         payload.length ≤ specializedPayloadBound n u J (baseWidth 3 p.t) d ∧
--         PayloadMeaning p ps P u J n f theta s j payload ∧
--         Eval FactorTableProgram.literalIteration k
--           (⟨regs,FactorTableProgram.literalReady s (List.replicate j true) acc⟩ : FactorTableProgram.OuterData)
--           (⟨rf,FactorTableProgram.literalReady s (List.replicate j true)
--             (Encoding.frame (Encoding.encodeNat j)++Encoding.frame payload++acc)⟩ : FactorTableProgram.OuterData)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.specializedPayloadBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.OuterStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.basePort` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalReady` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.projectBase` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.stream` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.StagedInput` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.sourceCallData` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input` (definitions bundle `OAIQ081S170` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.PayloadMeaning` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.specializedLiteralWork` (definitions bundle `OAIQ081S184` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalIteration` (definitions bundle `OAIQ081S189` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` and `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.command_native_resources` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.native_literal)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}

theorem native_literal {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f S j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d)
    (s : FactorTableProgram.OuterStore) (acc : List Bool)
    (h : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
      (FactorTableProgram.projectBase s) n)
    (hsource : ∀ regs : Fin 16 → Bool, SourceReady.Input p ps P
      (projectState id FactorTableProgram.basePort (sourceCallData s j acc regs)) j n f S)
    (hj : j < n) (hn : n ≤ S) (hf : f ≤ S)
    (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (h545 : s 545 = []) (h555 : s 555 = []) (h557 : s 557 = [])
    (hm : (s 575).length = n) (hmask : (s 857).length = n) (htmp : s 881 = [])
    (regs : Fin 16 → Bool) :
    ∃ payload k rf, k ≤ specializedLiteralWork p u J n S (s 574).length ∧
      payload.length ≤ specializedPayloadBound n u J (baseWidth 3 p.t) d ∧
      PayloadMeaning p ps P u J n f theta s j payload ∧
      Eval FactorTableProgram.literalIteration k
        (⟨regs,FactorTableProgram.literalReady s (List.replicate j true) acc⟩ : FactorTableProgram.OuterData)
        (⟨rf,FactorTableProgram.literalReady s (List.replicate j true)
          (Encoding.frame (Encoding.encodeNat j)++Encoding.frame payload++acc)⟩ : FactorTableProgram.OuterData) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end
