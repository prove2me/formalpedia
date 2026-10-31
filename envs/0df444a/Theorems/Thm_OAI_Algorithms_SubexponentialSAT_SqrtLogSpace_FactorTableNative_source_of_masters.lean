-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableNative_source_of_masters
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.source_of_masters
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:55:13.938423+00:00
-- url     : https://prove2.me/theorems/da7e85f8-b1dd-4538-a1e1-955dcca5374e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.source_of_masters: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.source_of_masters` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative`, with `open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram`, `open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram`, `open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes`):
--
--   ```lean
--   theorem source_of_masters {r Q d n J S f B : ℕ}
--       (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
--       (P : PackingData (Fin ps.length) (UniversalType r Q 1))
--       (a : FactorTableProgram.OuterData) (theta : Coeff (baseWidth 3 p.t) d)
--       (hscalar : ScalarMasters p.t p.model p.modulus p.cache J p.R theta
--         (projectState id FactorTableProgram.basePort a) n)
--       (hmasters : SourceMasters p ps P (projectState id FactorTableProgram.basePort a))
--       (hf : a.stacks 556 = List.replicate f true)
--       (hincoming : ∀ i, (a.stacks i).length ≤ B)
--       (hsize : 1029*B+99 ≤ S)
--       (harray : (p.R+1)*(d*baseWidth 3 p.t) ≤ S) (hcount : p.R+1 ≤ S)
--       (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
--       (hinc : ps.length ≤ S) :
--       SourceReady.Input p ps P (projectState id FactorTableProgram.basePort
--         (FactorTableProgram.staged a)) 0 n f S
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.basePort` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.encodeType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata.value` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.MetadataBound` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.OuterData` (definitions bundle `OAIQ081S142` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.ScalarMasters` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.staged` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input` (definitions bundle `OAIQ081S170` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.SourceMasters` (definitions bundle `OAIQ081S172` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.command_native_resources` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.source_of_masters)

import Mathlib
import Definitions.Def_OAIQ081S170
import Definitions.Def_OAIQ081S172

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

theorem source_of_masters {r Q d n J S f B : ℕ}
    (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : FactorTableProgram.OuterData) (theta : Coeff (baseWidth 3 p.t) d)
    (hscalar : ScalarMasters p.t p.model p.modulus p.cache J p.R theta
      (projectState id FactorTableProgram.basePort a) n)
    (hmasters : SourceMasters p ps P (projectState id FactorTableProgram.basePort a))
    (hf : a.stacks 556 = List.replicate f true)
    (hincoming : ∀ i, (a.stacks i).length ≤ B)
    (hsize : 1029*B+99 ≤ S)
    (harray : (p.R+1)*(d*baseWidth 3 p.t) ≤ S) (hcount : p.R+1 ≤ S)
    (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
    (hinc : ps.length ≤ S) :
    SourceReady.Input p ps P (projectState id FactorTableProgram.basePort
      (FactorTableProgram.staged a)) 0 n f S := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end
