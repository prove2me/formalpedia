-- Prove2me | Theorems.Thm_OAI_TuringRigidity_CohenAbsorptionGeneric_product_generic_absorption
-- name    : OAI.TuringRigidity.CohenAbsorptionGeneric.product_generic_absorption
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:35:32.539392+00:00
-- url     : https://prove2.me/theorems/55efcc16-de93-4a7a-80a4-d0a3d88373b4
-- title:
--   OAI.TuringRigidity.CohenAbsorptionGeneric.product_generic_absorption: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.CohenAbsorptionGeneric.product_generic_absorption` of [lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenAbsorptionGeneric.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenAbsorptionGeneric.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.CohenAbsorptionGeneric`, with `open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations`, `open InternalRegularAlgebra InternalProjectedGeneric`):
--
--   ```lean
--   theorem product_generic_absorption (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
--       (hq : q ∈ M) (hct : InternallyCountable M q) :
--       ∃ c ∈ M,
--         (∀ z, z ∈ c ↔ ∃ p ∈ q, ∃ s ∈ CohenGroundPoset.conditions ZFSet.omega,
--           z = TaggedProductConditions.code p s) ∧
--         ∀ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G →
--           ∃ W : GenericFilter (Conditions InternalCohen.conditions),
--             AtomicForcing.GroundGeneric M W ∧
--               genericExtensionSet M InternalCohen.conditions W.carrier =
--                 genericExtensionSet M c G.carrier
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet` and `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.InternallyCountable` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenGroundPoset.conditions`, `OAI.TuringRigidity.InternalCohen.conditions` and `OAI.TuringRigidity.TaggedProductConditions.code` (definitions bundle `OAIQ064A003` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.CohenManyAbsorption.same_generics_absorption` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenAbsorptionGeneric.lean (declaration OAI.TuringRigidity.CohenAbsorptionGeneric.product_generic_absorption)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A002
import Definitions.Def_OAIQ064A003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenAbsorptionGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem product_generic_absorption (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q) :
    ∃ c ∈ M,
      (∀ z, z ∈ c ↔ ∃ p ∈ q, ∃ s ∈ CohenGroundPoset.conditions ZFSet.omega,
        z = TaggedProductConditions.code p s) ∧
      ∀ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G →
        ∃ W : GenericFilter (Conditions InternalCohen.conditions),
          AtomicForcing.GroundGeneric M W ∧
            genericExtensionSet M InternalCohen.conditions W.carrier =
              genericExtensionSet M c G.carrier := by
  sorry

end TuringRigidity.CohenAbsorptionGeneric

end OAI
end
