-- Prove2me | Theorems.Thm_OAI_TuringRigidity_InternalBooleanIntermediate_internal_boolean_intermediate
-- name    : OAI.TuringRigidity.InternalBooleanIntermediate.internal_boolean_intermediate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:39:47.564402+00:00
-- url     : https://prove2.me/theorems/ecf28fce-7aa7-4fb8-89b8-b61eeb9eb10c
-- title:
--   OAI.TuringRigidity.InternalBooleanIntermediate.internal_boolean_intermediate: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.InternalBooleanIntermediate.internal_boolean_intermediate` of [lean/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanIntermediate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanIntermediate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.InternalBooleanIntermediate`, with `open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames`, `open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits`, `open InternalProjectedGeneric InternalBooleanTop InternalBooleanName InternalBooleanExtension`):
--
--   ```lean
--   theorem internal_boolean_intermediate (M c : ZFSet.{0}) [Top (Conditions c)]
--       (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
--       (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M) :
--       ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
--         (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
--         (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
--         A = InternalGeneratedAlgebra.generated c B Q (seeds c B E) ∧ Closed c B Q A ∧
--         ∃ σ : Name (Conditions (positive A)), σ.encode (label (positive A)) ∈ M ∧
--         ∀ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G → ⊤ ∈ G.carrier →
--           ∃ H : GenericFilter (Conditions (positive A)), AtomicForcing.GroundGeneric M H ∧
--             (∀ q, q ∈ H.carrier ↔ InternalBooleanGeneric.Hit G (label (positive A) q)) ∧
--             σ.val H.carrier = (InternalNiceName.nice E : Name (Conditions c)).val G.carrier ∧
--             Transitive (genericExtensionSet M (positive A) H.carrier) ∧
--             SourceT (genericExtensionSet M (positive A) H.carrier) ∧
--             M ⊆ genericExtensionSet M (positive A) H.carrier ∧
--             σ.val H.carrier ∈ genericExtensionSet M (positive A) H.carrier ∧
--             genericFilterSet (positive A) H.carrier ∈ genericExtensionSet M (positive A) H.carrier ∧
--             genericExtensionSet M (positive A) H.carrier ⊆ genericExtensionSet M c G.carrier
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.RecursiveNames.Name`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.TransitiveNameModel.label`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder`, `OAI.TuringRigidity.RecursiveNames.Name.encode` and `OAI.TuringRigidity.RecursiveNames.Name.val` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.InternalBooleanBits.seeds`, `OAI.TuringRigidity.InternalBooleanSyntax.Closed`, `OAI.TuringRigidity.InternalGeneratedAlgebra.generated`, `OAI.TuringRigidity.InternalProjectedGeneric.positive` and `OAI.TuringRigidity.InternalRegularAlgebra.IsCode` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.BoundedSetTheory.orbitGraph`, `OAI.TuringRigidity.InternalProjectedGeneric.codePreorder` and `OAI.TuringRigidity.TransitiveNameModel.genericFilterSet` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.InternalBooleanGeneric.Hit` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.InternalNiceName.nice` (definitions bundle `OAIQ064A006` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanIntermediate.lean (declaration OAI.TuringRigidity.InternalBooleanIntermediate.internal_boolean_intermediate)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A006

section

attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanIntermediate
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits
open InternalProjectedGeneric InternalBooleanTop InternalBooleanName InternalBooleanExtension
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem internal_boolean_intermediate (M c : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M) :
    ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
      (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
      (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
      A = InternalGeneratedAlgebra.generated c B Q (seeds c B E) ∧ Closed c B Q A ∧
      ∃ σ : Name (Conditions (positive A)), σ.encode (label (positive A)) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G → ⊤ ∈ G.carrier →
        ∃ H : GenericFilter (Conditions (positive A)), AtomicForcing.GroundGeneric M H ∧
          (∀ q, q ∈ H.carrier ↔ InternalBooleanGeneric.Hit G (label (positive A) q)) ∧
          σ.val H.carrier = (InternalNiceName.nice E : Name (Conditions c)).val G.carrier ∧
          Transitive (genericExtensionSet M (positive A) H.carrier) ∧
          SourceT (genericExtensionSet M (positive A) H.carrier) ∧
          M ⊆ genericExtensionSet M (positive A) H.carrier ∧
          σ.val H.carrier ∈ genericExtensionSet M (positive A) H.carrier ∧
          genericFilterSet (positive A) H.carrier ∈ genericExtensionSet M (positive A) H.carrier ∧
          genericExtensionSet M (positive A) H.carrier ⊆ genericExtensionSet M c G.carrier := by
  sorry

end TuringRigidity.InternalBooleanIntermediate

end OAI
end
