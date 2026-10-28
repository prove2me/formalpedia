-- Prove2me | Theorems.Thm_OAI_TuringRigidity_CohenProjectedNameLift_lift_projected_real_name
-- name    : OAI.TuringRigidity.CohenProjectedNameLift.lift_projected_real_name
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:38:40.092931+00:00
-- url     : https://prove2.me/theorems/3ba9f074-5920-4520-8043-e8e9cd433afa
-- title:
--   OAI.TuringRigidity.CohenProjectedNameLift.lift_projected_real_name: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.CohenProjectedNameLift.lift_projected_real_name` of [lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenProjectedNameLift.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenProjectedNameLift.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.CohenProjectedNameLift`, with `open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing`, `open CohenGroundPoset InternalCohenRestriction InternalCohenPartition InternalCohenProjectedGeneric`):
--
--   ```lean
--   theorem lift_projected_real_name (M A B : ZFSet.{0})
--       (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
--       (τ : Name (Conditions (conditions B))) (hτ : τ.encode (label (conditions B)) ∈ M) :
--       ∃ y : Name (Conditions (conditions A)), y.encode (label (conditions A)) ∈ M ∧
--         (∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
--           τ.val (projected A B hBA G).carrier ⊆ ZFSet.omega →
--             y.val G.carrier = τ.val (projected A B hBA G).carrier) ∧
--         ∀ a : Conditions (conditions A) ≃o Conditions (conditions A),
--           (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
--           ∀ G : GenericFilter (Conditions (conditions A)),
--             y.val (AutomorphismName.mapFilter a G).carrier = y.val G.carrier
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.RecursiveNames.Name`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.label`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder`, `OAI.TuringRigidity.RecursiveNames.Name.encode` and `OAI.TuringRigidity.RecursiveNames.Name.val` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.AutomorphismName.mapFilter` and `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenGroundPoset.conditions` and `OAI.TuringRigidity.InternalCohenRestriction.restrict` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.InternalCohenProjectedGeneric.projected` (definitions bundle `OAIQ064A006` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.BoundedForcing.projected_arithmetic_output_cone` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenProjectedNameLift.lean (declaration OAI.TuringRigidity.CohenProjectedNameLift.lift_projected_real_name)

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

namespace TuringRigidity.CohenProjectedNameLift
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenPartition InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

theorem lift_projected_real_name (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (τ : Name (Conditions (conditions B))) (hτ : τ.encode (label (conditions B)) ∈ M) :
    ∃ y : Name (Conditions (conditions A)), y.encode (label (conditions A)) ∈ M ∧
      (∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        τ.val (projected A B hBA G).carrier ⊆ ZFSet.omega →
          y.val G.carrier = τ.val (projected A B hBA G).carrier) ∧
      ∀ a : Conditions (conditions A) ≃o Conditions (conditions A),
        (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
        ∀ G : GenericFilter (Conditions (conditions A)),
          y.val (AutomorphismName.mapFilter a G).carrier = y.val G.carrier := by
  sorry

end TuringRigidity.CohenProjectedNameLift

end OAI
end
