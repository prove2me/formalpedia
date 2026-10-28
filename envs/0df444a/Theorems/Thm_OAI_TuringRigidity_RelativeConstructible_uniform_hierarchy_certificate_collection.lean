-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_uniform_hierarchy_certificate_collection
-- name    : OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate_collection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:47:28.433694+00:00
-- url     : https://prove2.me/theorems/f7506743-1744-4767-99b5-a981c8148e26
-- title:
--   OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate_collection: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate_collection` of [lean/OAI/Computability/DegreeRigidity/Constructibility/CollectionHierarchySyntax.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/CollectionHierarchySyntax.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding`, `open BoundedDefinability SetModelFunctions`):
--
--   ```lean
--   theorem uniform_hierarchy_certificate_collection (M R d q : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) (hColl : SigmaCollection M) (hs : seed R ∈ M) (hdM : d ∈ M) (hqM : q ∈ M)
--       (hd : Transitive d) (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) :
--       ∃ p : SigmaFormula, ∃ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ M) ∧
--         ∀ x ∈ d, ∀ f ∈ M, p.Realize M (cons f (cons x a)) ↔
--           ∃ r ∈ M, HierarchyGraph M (seed R) (_root_.OAI.TuringRigidity.BoundedSetTheory.hull d q x) r f
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.BoundedSetTheory.cons` and `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.RelativeConstructible.seed` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula`, `OAI.TuringRigidity.BoundedSetTheory.SigmaReplacement` and `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.Realize` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.BoundedSetTheory.hull` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.BoundedSetTheory.SigmaCollection` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RelativeConstructible.HierarchyGraph` and `OAI.TuringRigidity.SetModelFunctions.Context` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.internal_hierarchyGraph_collection` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/CollectionHierarchySyntax.lean (declaration OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate_collection)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A006
import Definitions.Def_OAIQ064A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem uniform_hierarchy_certificate_collection (M R d q : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) (hColl : SigmaCollection M) (hs : seed R ∈ M) (hdM : d ∈ M) (hqM : q ∈ M)
    (hd : Transitive d) (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) :
    ∃ p : SigmaFormula, ∃ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ M) ∧
      ∀ x ∈ d, ∀ f ∈ M, p.Realize M (cons f (cons x a)) ↔
        ∃ r ∈ M, HierarchyGraph M (seed R) (_root_.OAI.TuringRigidity.BoundedSetTheory.hull d q x) r f := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
