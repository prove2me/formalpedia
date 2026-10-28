-- Prove2me | Theorems.Thm_OAI_TuringRigidity_OriginalRealDefinitionTransport_original_definition_transport
-- name    : OAI.TuringRigidity.OriginalRealDefinitionTransport.original_definition_transport
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:49:10.372182+00:00
-- url     : https://prove2.me/theorems/19ef3e23-8f3d-4c56-9122-2d778e6d0912
-- title:
--   OAI.TuringRigidity.OriginalRealDefinitionTransport.original_definition_transport: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.OriginalRealDefinitionTransport.original_definition_transport` of [lean/OAI/Computability/DegreeRigidity/Representation/OriginalRealDefinitionTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/OriginalRealDefinitionTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.OriginalRealDefinitionTransport`, with `open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames`, `open CohenGroundPoset InternalCountableOrdinals RelativeConstructible ElementaryModel`):
--
--   ```lean
--   theorem original_definition_transport (M K : ZFSet.{0})
--       (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
--       (τ f : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
--       (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
--       (hf : f.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
--       (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
--       (hG : AtomicForcing.GroundGeneric M G) (hreal : τ.val G.carrier ⊆ ZFSet.omega)
--       (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (φ : SentenceForm)
--       (hX : τ.val G.carrier ∈ level (groundReals
--         (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)) δ)
--       (hdef : f.val G.carrier = definedSubset (level (groundReals
--         (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)) δ)
--           φ (fun _ : Fin φ.bound => τ.val G.carrier)) :
--       Transported M K G f (τ.val G.carrier) δ φ
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.RecursiveNames.Name`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.TransitiveNameModel.label`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder`, `OAI.TuringRigidity.RecursiveNames.Name.encode` and `OAI.TuringRigidity.RecursiveNames.Name.val` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.ElementaryModel.SentenceForm`, `OAI.TuringRigidity.InternalCountableOrdinals.FirstUncountable`, `OAI.TuringRigidity.RelativeConstructible.groundReals` and `OAI.TuringRigidity.ElementaryModel.SentenceForm.bound` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenGroundPoset.conditions` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.RelativeConstructible.definedSubset` and `OAI.TuringRigidity.RelativeConstructible.level` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.OriginalRealDefinitionTransport.Transported` (definitions bundle `OAIQ064A008` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/OriginalRealDefinitionTransport.lean (declaration OAI.TuringRigidity.OriginalRealDefinitionTransport.original_definition_transport)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008

section

attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OriginalRealDefinitionTransport
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalCountableOrdinals RelativeConstructible ElementaryModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

theorem original_definition_transport (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (τ f : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
    (hf : f.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : AtomicForcing.GroundGeneric M G) (hreal : τ.val G.carrier ⊆ ZFSet.omega)
    (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (φ : SentenceForm)
    (hX : τ.val G.carrier ∈ level (groundReals
      (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)) δ)
    (hdef : f.val G.carrier = definedSubset (level (groundReals
      (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)) δ)
        φ (fun _ : Fin φ.bound => τ.val G.carrier)) :
    Transported M K G f (τ.val G.carrier) δ φ := by
  sorry

end TuringRigidity.OriginalRealDefinitionTransport

end OAI
end
