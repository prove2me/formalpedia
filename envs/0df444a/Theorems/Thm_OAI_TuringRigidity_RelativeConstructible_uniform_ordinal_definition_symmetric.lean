-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_uniform_ordinal_definition_symmetric
-- name    : OAI.TuringRigidity.RelativeConstructible.uniform_ordinal_definition_symmetric
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:47:42.605428+00:00
-- url     : https://prove2.me/theorems/2439546b-9c9e-471e-aef1-17a24712c2ac
-- title:
--   OAI.TuringRigidity.RelativeConstructible.uniform_ordinal_definition_symmetric: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.uniform_ordinal_definition_symmetric` of [lean/OAI/Computability/DegreeRigidity/Constructibility/UniformDefinitionSymmetry.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/UniformDefinitionSymmetry.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing`):
--
--   ```lean
--   theorem uniform_ordinal_definition_symmetric (M c : ZFSet.{0})
--       [OrderTop (Conditions c)] (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
--       (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (X : ZFSet.{0}) (hX : X ∈ M)
--       (φ : ElementaryModel.SentenceForm) :
--       ∃ f : Name (Conditions c), f.encode (label c) ∈ M ∧
--         (∀ G : GenericFilter (Conditions c), GroundGeneric M G →
--           f.val G.carrier = definedSubset
--             (level (groundReals (genericExtensionSet M c G.carrier)) δ)
--               φ (fun _ : Fin φ.bound => X)) ∧
--         ∀ w ∈ M, ∀ e : Conditions c ≃o Conditions c,
--           (∀ p q, ZFSet.pair (label c p) (label c q) ∈ w ↔ q = e p) →
--           ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
--             f.val (AutomorphismName.mapFilter e G).carrier = f.val G.carrier
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.RecursiveNames.Name`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.TransitiveNameModel.label`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder`, `OAI.TuringRigidity.RecursiveNames.Name.encode` and `OAI.TuringRigidity.RecursiveNames.Name.val` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.ElementaryModel.SentenceForm`, `OAI.TuringRigidity.RelativeConstructible.groundReals` and `OAI.TuringRigidity.ElementaryModel.SentenceForm.bound` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.AutomorphismName.mapFilter` and `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.RelativeConstructible.definedSubset` and `OAI.TuringRigidity.RelativeConstructible.level` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.uniform_cohen_definition_extension` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/UniformDefinitionSymmetry.lean (declaration OAI.TuringRigidity.RelativeConstructible.uniform_ordinal_definition_symmetric)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem uniform_ordinal_definition_symmetric (M c : ZFSet.{0})
    [OrderTop (Conditions c)] (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (X : ZFSet.{0}) (hX : X ∈ M)
    (φ : ElementaryModel.SentenceForm) :
    ∃ f : Name (Conditions c), f.encode (label c) ∈ M ∧
      (∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        f.val G.carrier = definedSubset
          (level (groundReals (genericExtensionSet M c G.carrier)) δ)
            φ (fun _ : Fin φ.bound => X)) ∧
      ∀ w ∈ M, ∀ e : Conditions c ≃o Conditions c,
        (∀ p q, ZFSet.pair (label c p) (label c q) ∈ w ↔ q = e p) →
        ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
          f.val (AutomorphismName.mapFilter e G).carrier = f.val G.carrier := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
