-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_Construction_cofinal_one_real_definition
-- name    : OAI.TuringRigidity.RelativeConstructible.Construction.cofinal_one_real_definition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:51:16.921472+00:00
-- url     : https://prove2.me/theorems/0ec103e4-dd06-445e-be8f-9cbfd602ef4d
-- title:
--   OAI.TuringRigidity.RelativeConstructible.Construction.cofinal_one_real_definition: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.Construction.cofinal_one_real_definition` of [lean/OAI/Computability/DegreeRigidity/Constructibility/OneRealConstructionDefinition.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/OneRealConstructionDefinition.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open ElementaryModel BoundedSetTheory TransitiveNameModel OrdinalCoding`):
--
--   ```lean
--   theorem Construction.cofinal_one_real_definition (t : Construction.{u}) :
--       ∃ p : SentenceForm, p.bound ≤ 2 ∧
--         ∀ M : ZFSet.{u}, Transitive M → SourceT M →
--         ∀ P : Oracle, P ∈ modelReals M → t.Certified (groundReals M) P → t.Indexed M →
--         ∀ θ : Ordinal.{u}, θ.toZFSet ∈ M →
--         ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧ θ < β ∧ realSeedOffset < β ∧
--           (heightDomainIndex (paddedCode t.ordinalVector β)).toZFSet ∈ M ∧
--           (realCode P ∈ level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β))) ∧
--           t.value (groundReals M) P = definedSubset
--             (level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β))) p
--             (fun _ : Fin p.bound => realCode P)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.ElementaryModel.SentenceForm`, `OAI.TuringRigidity.OrdinalCoding.paddedCode`, `OAI.TuringRigidity.RelativeConstructible.groundReals`, `OAI.TuringRigidity.RelativeConstructible.heightDomainIndex`, `OAI.TuringRigidity.RelativeConstructible.realSeedOffset` and `OAI.TuringRigidity.ElementaryModel.SentenceForm.bound` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` and `OAI.TuringRigidity.BoundedSetTheory.realCode` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.BoundedSetTheory.modelReals` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RelativeConstructible.Construction`, `OAI.TuringRigidity.RelativeConstructible.definedSubset`, `OAI.TuringRigidity.RelativeConstructible.level`, `OAI.TuringRigidity.RelativeConstructible.Construction.Certified`, `OAI.TuringRigidity.RelativeConstructible.Construction.Indexed` and `OAI.TuringRigidity.RelativeConstructible.Construction.value` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.RelativeConstructible.Construction.ordinalVector` and `OAI.TuringRigidity.RelativeConstructible.Construction.ownRealsMembership` (definitions bundle `OAIQ064A008` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.FullSetForcing.prescribed_one_real_names` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/OneRealConstructionDefinition.lean (declaration OAI.TuringRigidity.RelativeConstructible.Construction.cofinal_one_real_definition)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel OrdinalCoding
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

theorem Construction.cofinal_one_real_definition (t : Construction.{u}) :
    ∃ p : SentenceForm, p.bound ≤ 2 ∧
      ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ P : Oracle, P ∈ modelReals M → t.Certified (groundReals M) P → t.Indexed M →
      ∀ θ : Ordinal.{u}, θ.toZFSet ∈ M →
      ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧ θ < β ∧ realSeedOffset < β ∧
        (heightDomainIndex (paddedCode t.ordinalVector β)).toZFSet ∈ M ∧
        (realCode P ∈ level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β))) ∧
        t.value (groundReals M) P = definedSubset
          (level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β))) p
          (fun _ : Fin p.bound => realCode P) := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
