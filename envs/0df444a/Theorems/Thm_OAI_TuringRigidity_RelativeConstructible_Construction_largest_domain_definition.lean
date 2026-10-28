-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_Construction_largest_domain_definition
-- name    : OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:51:40.88698+00:00
-- url     : https://prove2.me/theorems/0ca7a965-0507-417d-83b8-37c735881842
-- title:
--   OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition` of [lean/OAI/Computability/DegreeRigidity/Constructibility/ConstructionHeightDomains.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/ConstructionHeightDomains.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open ElementaryModel BoundedSetTheory TransitiveNameModel`):
--
--   ```lean
--   theorem Construction.largest_domain_definition (t : Construction.{u}) :
--       ∃ q : SentenceForm, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
--         ∀ P : Oracle, P ∈ modelReals M → t.Certified (groundReals M) P → t.Indexed M →
--           ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧
--             ∀ a : Ordinal.{u}, a.toZFSet ∈ M → β ≤ a →
--               let R := groundReals M
--               let δ := a - ordinalHeight (seed R) + 1
--               δ.toZFSet ∈ M ∧ t.value R P ∈ level R δ ∧
--               (∀ i, t.ordinalInputs P i ∈ level R δ) ∧
--               (∀ e : ℕ → ZFSet.{u}, e 0 ∈ level R δ →
--                 (largestOrdinalSentence.Sat (level R δ : Set ZFSet) e ↔ e 0 = a.toZFSet)) ∧
--               ∀ z ∈ level R δ,
--                 q.Sat (level R δ : Set ZFSet) (cons z (t.ordinalInputs P)) ↔ z ∈ t.value R P
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.BoundedSetTheory.cons` and `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.ElementaryModel.SentenceForm`, `OAI.TuringRigidity.RelativeConstructible.groundReals`, `OAI.TuringRigidity.RelativeConstructible.ordinalHeight` and `OAI.TuringRigidity.RelativeConstructible.seed` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` and `OAI.TuringRigidity.ElementaryModel.SentenceForm.Sat` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.BoundedSetTheory.modelReals` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RelativeConstructible.Construction`, `OAI.TuringRigidity.RelativeConstructible.level`, `OAI.TuringRigidity.RelativeConstructible.Construction.Certified`, `OAI.TuringRigidity.RelativeConstructible.Construction.Indexed` and `OAI.TuringRigidity.RelativeConstructible.Construction.value` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.RelativeConstructible.largestOrdinalSentence` and `OAI.TuringRigidity.RelativeConstructible.Construction.ordinalInputs` (definitions bundle `OAIQ064A008` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.Construction.cofinal_one_real_definition` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/ConstructionHeightDomains.lean (declaration OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition)

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
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

theorem Construction.largest_domain_definition (t : Construction.{u}) :
    ∃ q : SentenceForm, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ P : Oracle, P ∈ modelReals M → t.Certified (groundReals M) P → t.Indexed M →
        ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧
          ∀ a : Ordinal.{u}, a.toZFSet ∈ M → β ≤ a →
            let R := groundReals M
            let δ := a - ordinalHeight (seed R) + 1
            δ.toZFSet ∈ M ∧ t.value R P ∈ level R δ ∧
            (∀ i, t.ordinalInputs P i ∈ level R δ) ∧
            (∀ e : ℕ → ZFSet.{u}, e 0 ∈ level R δ →
              (largestOrdinalSentence.Sat (level R δ : Set ZFSet) e ↔ e 0 = a.toZFSet)) ∧
            ∀ z ∈ level R δ,
              q.Sat (level R δ : Set ZFSet) (cons z (t.ordinalInputs P)) ↔ z ∈ t.value R P := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
