-- Prove2me | Theorems.Thm_OAI_TuringRigidity_CohenNiceNameConstruction_internal_nice_name
-- name    : OAI.TuringRigidity.CohenNiceNameConstruction.internal_nice_name
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:39:16.781498+00:00
-- url     : https://prove2.me/theorems/aa664d0f-2ebf-4208-b0c2-33b1561b4038
-- title:
--   OAI.TuringRigidity.CohenNiceNameConstruction.internal_nice_name: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.CohenNiceNameConstruction.internal_nice_name` of [lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenNiceNameConstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenNiceNameConstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.CohenNiceNameConstruction`, with `open TransitiveNameModel BoundedSetTheory RecursiveNames AtomicForcing CountableForcing`, `open CohenGroundPoset CohenAntichainSelector CohenInternalDecision InternalPositiveNameFamily`):
--
--   ```lean
--   theorem internal_nice_name (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
--       (hA : A ∈ M) (τ : Name (Conditions (conditions A))) (hτ : τ.encode (label (conditions A)) ∈ M) :
--       ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
--         (∀ n, E n ∈ M ∧ Selected (conditions A) (positive τ n) (E n)) ∧
--         (InternalNiceName.nice E : Name (Conditions (conditions A))).encode (label (conditions A)) ∈ M ∧
--         (∃ S ∈ M, S ⊆ A ∧ (∀ x, x ∈ S ↔ ∃ n, ∃ p ∈ E n, x ∈ CohenInternalSupport.supportSet A p) ∧
--           (S = ∅ ∨ InternallyCountable M S)) ∧
--         ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
--           τ.val G.carrier ⊆ ZFSet.omega →
--           (InternalNiceName.nice E : Name (Conditions (conditions A))).val G.carrier = τ.val G.carrier
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.RecursiveNames.Name`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.label`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder`, `OAI.TuringRigidity.RecursiveNames.Name.encode` and `OAI.TuringRigidity.RecursiveNames.Name.val` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.InternallyCountable` and `OAI.TuringRigidity.CohenAntichainSelector.Selected` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.BoundedSetTheory.orbitGraph`, `OAI.TuringRigidity.CohenGroundPoset.conditions` and `OAI.TuringRigidity.CohenInternalSupport.supportSet` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.CohenNiceNameConstruction.cohenTop` and `OAI.TuringRigidity.InternalNiceName.nice` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.InternalPositiveNameFamily.positive` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.CohenProjectedNameLift.lift_projected_real_name` and `OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenNiceNameConstruction.lean (declaration OAI.TuringRigidity.CohenNiceNameConstruction.internal_nice_name)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A006
import Definitions.Def_OAIQ064A007

section

attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenNiceNameConstruction
open TransitiveNameModel BoundedSetTheory RecursiveNames AtomicForcing CountableForcing
open CohenGroundPoset CohenAntichainSelector CohenInternalDecision InternalPositiveNameFamily
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

attribute [local instance] cohenTop

theorem internal_nice_name (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (τ : Name (Conditions (conditions A))) (hτ : τ.encode (label (conditions A)) ∈ M) :
    ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
      (∀ n, E n ∈ M ∧ Selected (conditions A) (positive τ n) (E n)) ∧
      (InternalNiceName.nice E : Name (Conditions (conditions A))).encode (label (conditions A)) ∈ M ∧
      (∃ S ∈ M, S ⊆ A ∧ (∀ x, x ∈ S ↔ ∃ n, ∃ p ∈ E n, x ∈ CohenInternalSupport.supportSet A p) ∧
        (S = ∅ ∨ InternallyCountable M S)) ∧
      ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        τ.val G.carrier ⊆ ZFSet.omega →
        (InternalNiceName.nice E : Name (Conditions (conditions A))).val G.carrier = τ.val G.carrier := by
  sorry

end TuringRigidity.CohenNiceNameConstruction

end OAI
end
