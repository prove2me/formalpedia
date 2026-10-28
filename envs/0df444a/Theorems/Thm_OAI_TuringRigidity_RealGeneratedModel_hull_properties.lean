-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RealGeneratedModel_hull_properties
-- name    : OAI.TuringRigidity.RealGeneratedModel.hull_properties
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:50:27.516968+00:00
-- url     : https://prove2.me/theorems/2e1a42b6-1c67-4b40-b441-914bc3a73448
-- title:
--   OAI.TuringRigidity.RealGeneratedModel.hull_properties: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RealGeneratedModel.hull_properties` of [lean/OAI/Computability/DegreeRigidity/Representation/RealGeneratedModel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/RealGeneratedModel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RealGeneratedModel`, with `open TransitiveNameModel BoundedSetTheory CountableForcing`, `open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits`, `open InternalGeneratedAlgebra InternalProjectedGeneric InternalBooleanTop`):
--
--   ```lean
--   theorem hull_properties (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
--       (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
--       (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
--       (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
--       (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
--       (hAe : A = generated c B Q (seeds c B E))
--       (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈ G.carrier) :
--       let X := (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier
--       Contains M X (hull M X) ∧
--         genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ∈ hull M X ∧
--         hull M X ⊆ genericExtensionSet M c G.carrier
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` and `OAI.TuringRigidity.RecursiveNames.Name.val` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.InternalBooleanBits.seeds`, `OAI.TuringRigidity.InternalBooleanSyntax.Closed`, `OAI.TuringRigidity.InternalGeneratedAlgebra.generated`, `OAI.TuringRigidity.InternalProjectedGeneric.positive` and `OAI.TuringRigidity.InternalRegularAlgebra.IsCode` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.BoundedSetTheory.orbitGraph`, `OAI.TuringRigidity.InternalProjectedGeneric.codePreorder` and `OAI.TuringRigidity.TransitiveNameModel.genericFilterSet` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.InternalNiceName.nice` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RealGeneratedModel.Contains` and `OAI.TuringRigidity.RealGeneratedModel.hull` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.InternalProjectedGeneric.projected` (definitions bundle `OAIQ064A008` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/RealGeneratedModel.lean (declaration OAI.TuringRigidity.RealGeneratedModel.hull_properties)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008

section

attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RealGeneratedModel
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits
open InternalGeneratedAlgebra InternalProjectedGeneric InternalBooleanTop

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  codeOrder codePreorder

theorem hull_properties (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hAe : A = generated c B Q (seeds c B E))
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈ G.carrier) :
    let X := (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier
    Contains M X (hull M X) ∧
      genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ∈ hull M X ∧
      hull M X ⊆ genericExtensionSet M c G.carrier := by
  sorry

end TuringRigidity.RealGeneratedModel

end OAI
end
