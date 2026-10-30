-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableNative_command_native_resources
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.command_native_resources
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:04:59.528993+00:00
-- url     : https://prove2.me/theorems/4ad8dca7-2ad0-4abd-bcdc-88448640c203
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.command_native_resources: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.command_native_resources` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative`, with `open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram`, `open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram`, `open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes`):
--
--   ```lean
--   theorem command_native_resources {r Q d u J n f B S : ℕ}
--       {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
--       {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
--       {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
--       (h : Ready p ps P u J n f B S theta a) :
--       let K := specializedLiteralWork p u J n S ((FactorTableProgram.staged a).stacks 574).length
--       let L := specializedPayloadBound n u J (baseWidth 3 p.t) d
--       ∃ (incidence : Fin n → List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d))
--         (steps : ℕ) (e : FactorTableProgram.OuterData),
--         (∀ v, TruncatedRingProgram.Good ∅ u J (incidence v)) ∧
--         (∀ v, (MomentsProgram.Product.bytes (incidence v)).length ≤ L) ∧
--         (∀ v, PayloadMeaning p ps P u J n f theta (FactorTableProgram.staged a).stacks
--           v.val (MomentsProgram.Product.bytes (incidence v))) ∧
--         steps ≤ FactorTableSpace.commandBudget B n K L ∧
--         Trace FactorTableProgram.program steps (a.withPC (some FactorTableProgram.program.entry)) (e.withPC none) ∧
--         e.stacks 62 = Squarefree.Program.lookupRecords
--           (HashCircuitProgram.incidenceEntries (fun (_ : Unit) v => MomentsProgram.Product.bytes (incidence v)) ()) ∧
--         (∀ i, i ∉ FactorTableSpace.writtenPorts → e.stacks i = a.stacks i) ∧
--         (∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → e.stacks i = []) ∧
--         ∀ prefixSteps intermediate, prefixSteps ≤ steps →
--           Trace FactorTableProgram.program prefixSteps (a.withPC (some FactorTableProgram.program.entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length ≤ 896*B+FactorTableSpace.commandBudget B n K L
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.specializedPayloadBound` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.incidenceEntries` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.lookupRecords` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.writtenPorts` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.commandBudget` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.OuterData` (definitions bundle `OAIQ081S142` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.staged` (definitions bundle `OAIQ081S170` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.Ready` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.PayloadMeaning` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.specializedLiteralWork` (definitions bundle `OAIQ081S184` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.command` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.program` (definitions bundle `OAIQ081S189` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.prepareIncidence_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.command_native_resources)

import Mathlib
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

theorem command_native_resources {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (h : Ready p ps P u J n f B S theta a) :
    let K := specializedLiteralWork p u J n S ((FactorTableProgram.staged a).stacks 574).length
    let L := specializedPayloadBound n u J (baseWidth 3 p.t) d
    ∃ (incidence : Fin n → List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d))
      (steps : ℕ) (e : FactorTableProgram.OuterData),
      (∀ v, TruncatedRingProgram.Good ∅ u J (incidence v)) ∧
      (∀ v, (MomentsProgram.Product.bytes (incidence v)).length ≤ L) ∧
      (∀ v, PayloadMeaning p ps P u J n f theta (FactorTableProgram.staged a).stacks
        v.val (MomentsProgram.Product.bytes (incidence v))) ∧
      steps ≤ FactorTableSpace.commandBudget B n K L ∧
      Trace FactorTableProgram.program steps (a.withPC (some FactorTableProgram.program.entry)) (e.withPC none) ∧
      e.stacks 62 = Squarefree.Program.lookupRecords
        (HashCircuitProgram.incidenceEntries (fun (_ : Unit) v => MomentsProgram.Product.bytes (incidence v)) ()) ∧
      (∀ i, i ∉ FactorTableSpace.writtenPorts → e.stacks i = a.stacks i) ∧
      (∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → e.stacks i = []) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace FactorTableProgram.program prefixSteps (a.withPC (some FactorTableProgram.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896*B+FactorTableSpace.commandBudget B n K L := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end
