-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_uniform_cohen_definition_extension
-- name    : OAI.TuringRigidity.RelativeConstructible.uniform_cohen_definition_extension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:47:13.670084+00:00
-- url     : https://prove2.me/theorems/e813124c-d055-42b8-ac45-87199681a7b9
-- title:
--   OAI.TuringRigidity.RelativeConstructible.uniform_cohen_definition_extension: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.uniform_cohen_definition_extension` of [lean/OAI/Computability/DegreeRigidity/Effective/UniformCohenDefinitionExtension.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Effective/UniformCohenDefinitionExtension.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing BoundedForcing`, `open CohenGroundPoset`):
--
--   ```lean
--   theorem uniform_cohen_definition_extension (M A I ρ : ZFSet.{0})
--       (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
--       (hA : A ∈ M) (hI : I ∈ M) (hρ : ρ ∈ M)
--       (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (X : ZFSet.{0}) (hX : X ∈ M)
--       (φ : ElementaryModel.SentenceForm)
--       (G₀ : GenericFilter (Conditions (conditions A))) (hG₀ : GroundGeneric M G₀)
--       (h₀ : OwnDegreeExtension (genericExtensionSet M (conditions A) G₀.carrier) I ρ
--         (definedSubset (level (groundReals (genericExtensionSet M (conditions A) G₀.carrier)) δ)
--           φ (fun _ : Fin φ.bound => X))) :
--       ∃ f : Name (Conditions (conditions A)), f.encode (label (conditions A)) ∈ M ∧
--         ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
--           f.val G.carrier = definedSubset
--             (level (groundReals (genericExtensionSet M (conditions A) G.carrier)) δ)
--               φ (fun _ : Fin φ.bound => X) ∧
--           OwnDegreeExtension (genericExtensionSet M (conditions A) G.carrier) I ρ (f.val G.carrier)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.RecursiveNames.Name`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.TransitiveNameModel.label`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder`, `OAI.TuringRigidity.RecursiveNames.Name.encode` and `OAI.TuringRigidity.RecursiveNames.Name.val` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.ElementaryModel.SentenceForm`, `OAI.TuringRigidity.RelativeConstructible.groundReals` and `OAI.TuringRigidity.ElementaryModel.SentenceForm.bound` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedForcing.OwnDegreeExtension` and `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenGroundPoset.conditions` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.RelativeConstructible.definedSubset` and `OAI.TuringRigidity.RelativeConstructible.level` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Effective/UniformCohenDefinitionExtension.lean (declaration OAI.TuringRigidity.RelativeConstructible.uniform_cohen_definition_extension)

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
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing BoundedForcing
open CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem uniform_cohen_definition_extension (M A I ρ : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hA : A ∈ M) (hI : I ∈ M) (hρ : ρ ∈ M)
    (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (X : ZFSet.{0}) (hX : X ∈ M)
    (φ : ElementaryModel.SentenceForm)
    (G₀ : GenericFilter (Conditions (conditions A))) (hG₀ : GroundGeneric M G₀)
    (h₀ : OwnDegreeExtension (genericExtensionSet M (conditions A) G₀.carrier) I ρ
      (definedSubset (level (groundReals (genericExtensionSet M (conditions A) G₀.carrier)) δ)
        φ (fun _ : Fin φ.bound => X))) :
    ∃ f : Name (Conditions (conditions A)), f.encode (label (conditions A)) ∈ M ∧
      ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        f.val G.carrier = definedSubset
          (level (groundReals (genericExtensionSet M (conditions A) G.carrier)) δ)
            φ (fun _ : Fin φ.bound => X) ∧
        OwnDegreeExtension (genericExtensionSet M (conditions A) G.carrier) I ρ (f.val G.carrier) := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
