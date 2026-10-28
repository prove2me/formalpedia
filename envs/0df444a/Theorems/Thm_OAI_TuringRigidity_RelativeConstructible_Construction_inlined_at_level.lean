-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_Construction_inlined_at_level
-- name    : OAI.TuringRigidity.RelativeConstructible.Construction.inlined_at_level
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:52:16.968144+00:00
-- url     : https://prove2.me/theorems/050c7f8f-3c37-4f2c-a5c1-eee1ac3e6742
-- title:
--   OAI.TuringRigidity.RelativeConstructible.Construction.inlined_at_level: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.Construction.inlined_at_level` of [lean/OAI/Computability/DegreeRigidity/OrdinalCodes/LevelInlinedDefinition.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/OrdinalCodes/LevelInlinedDefinition.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic`, `open SetDegreeDecoding PersistentRestrictions`):
--
--   ```lean
--   theorem Construction.inlined_at_level (t : Construction.{u}) (M : ZFSet.{u})
--       (hM : Transitive M) (hT : SourceT M) (P : Oracle)
--       (hP : P ∈ modelReals M) (ht : t.Certified (groundReals M) P) (hi : t.Indexed M) :
--       ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
--         t.value (groundReals M) P ∈ level (groundReals M) γ ∧
--         (∀ i, t.singleInputs (groundReals M) P i ∈ level (groundReals M) γ) ∧
--         ∀ z ∈ level (groundReals M) γ,
--           t.singleMembership.Sat (level (groundReals M) γ : Set ZFSet)
--             (cons z (t.singleInputs (groundReals M) P)) ↔ z ∈ t.value (groundReals M) P
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.BoundedSetTheory.cons` and `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.RelativeConstructible.groundReals` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` and `OAI.TuringRigidity.ElementaryModel.SentenceForm.Sat` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.BoundedSetTheory.modelReals` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RelativeConstructible.Construction`, `OAI.TuringRigidity.RelativeConstructible.level`, `OAI.TuringRigidity.RelativeConstructible.Construction.Certified`, `OAI.TuringRigidity.RelativeConstructible.Construction.Indexed`, `OAI.TuringRigidity.RelativeConstructible.Construction.singleInputs` and `OAI.TuringRigidity.RelativeConstructible.Construction.value` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.RelativeConstructible.Construction.singleMembership` (definitions bundle `OAIQ064A008` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/OrdinalCodes/LevelInlinedDefinition.lean (declaration OAI.TuringRigidity.RelativeConstructible.Construction.inlined_at_level)

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
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
open SetDegreeDecoding PersistentRestrictions
universe u

theorem Construction.inlined_at_level (t : Construction.{u}) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (P : Oracle)
    (hP : P ∈ modelReals M) (ht : t.Certified (groundReals M) P) (hi : t.Indexed M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
      t.value (groundReals M) P ∈ level (groundReals M) γ ∧
      (∀ i, t.singleInputs (groundReals M) P i ∈ level (groundReals M) γ) ∧
      ∀ z ∈ level (groundReals M) γ,
        t.singleMembership.Sat (level (groundReals M) γ : Set ZFSet)
          (cons z (t.singleInputs (groundReals M) P)) ↔ z ∈ t.value (groundReals M) P := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
