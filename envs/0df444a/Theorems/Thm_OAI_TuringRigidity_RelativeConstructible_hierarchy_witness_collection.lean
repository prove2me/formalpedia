-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_hierarchy_witness_collection
-- name    : OAI.TuringRigidity.RelativeConstructible.hierarchy_witness_collection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:45:44.792814+00:00
-- url     : https://prove2.me/theorems/d28d449a-c017-4e8b-a882-350956f419ba
-- title:
--   OAI.TuringRigidity.RelativeConstructible.hierarchy_witness_collection: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.hierarchy_witness_collection` of [lean/OAI/Computability/DegreeRigidity/Constructibility/HierarchyWitnessCollection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/HierarchyWitnessCollection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding`, `open BoundedDefinability SetModelFunctions`):
--
--   ```lean
--   theorem hierarchy_witness_collection {M Q B s d r f : ZFSet.{u}} (C : Context M)
--       (hColl : SigmaCollection M) (hQ : Q ∈ M) (hB : B ∈ M)
--       (hq : ∀ p : SentenceForm, family p ∈ Q)
--       (hb : ∀ p : SentenceForm, supportGraph p ∈ B)
--       (hs : s ∈ M) (hd : d ∈ M) (hr : r ∈ M) (hf : f ∈ M)
--       (hg : HierarchyGraph M s d r f) :
--       ∃ W ∈ M, ∀ x ∈ d, ∃ c ∈ W, HierarchyRequest Q B s f r x c
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.ElementaryModel.SentenceForm` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SigmaCollection` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RelativeConstructible.HierarchyGraph`, `OAI.TuringRigidity.RelativeConstructible.HierarchyRequest`, `OAI.TuringRigidity.SentenceCoding.family`, `OAI.TuringRigidity.SentenceCoding.supportGraph` and `OAI.TuringRigidity.SetModelFunctions.Context` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.hierarchy_checked_at_levels` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/HierarchyWitnessCollection.lean (declaration OAI.TuringRigidity.RelativeConstructible.hierarchy_witness_collection)

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

theorem hierarchy_witness_collection {M Q B s d r f : ZFSet.{u}} (C : Context M)
    (hColl : SigmaCollection M) (hQ : Q ∈ M) (hB : B ∈ M)
    (hq : ∀ p : SentenceForm, family p ∈ Q)
    (hb : ∀ p : SentenceForm, supportGraph p ∈ B)
    (hs : s ∈ M) (hd : d ∈ M) (hr : r ∈ M) (hf : f ∈ M)
    (hg : HierarchyGraph M s d r f) :
    ∃ W ∈ M, ∀ x ∈ d, ∃ c ∈ W, HierarchyRequest Q B s f r x c := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
