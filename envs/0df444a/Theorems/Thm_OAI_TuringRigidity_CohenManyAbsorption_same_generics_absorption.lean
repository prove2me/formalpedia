-- Prove2me | Theorems.Thm_OAI_TuringRigidity_CohenManyAbsorption_same_generics_absorption
-- name    : OAI.TuringRigidity.CohenManyAbsorption.same_generics_absorption
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:35:29.364103+00:00
-- url     : https://prove2.me/theorems/0debad53-a861-4a03-baa9-2c90f741f4b0
-- title:
--   OAI.TuringRigidity.CohenManyAbsorption.same_generics_absorption: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.CohenManyAbsorption.same_generics_absorption` of [lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenManyAbsorption.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenManyAbsorption.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.CohenManyAbsorption`, with `open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset`):
--
--   ```lean
--   theorem same_generics_absorption (M q A a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
--       (hq : q ∈ M) (hct : InternallyCountable M q) (hA : A ∈ M) (ha : a ∈ M)
--       (hBA : ZFSet.prod {a} ZFSet.omega ⊆ A)
--       (G : GenericFilter (Conditions q)) (hG : AtomicForcing.GroundGeneric M G)
--       (L : GenericFilter (Conditions (conditions A)))
--       (hL : AtomicForcing.GroundGeneric (genericExtensionSet M q G.carrier) L) :
--       ∃ U : GenericFilter (Conditions (conditions A)), AtomicForcing.GroundGeneric M U ∧
--         genericExtensionSet M (conditions A) U.carrier =
--           genericExtensionSet (genericExtensionSet M q G.carrier) (conditions A) L.carrier
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet` and `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.InternallyCountable` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenGroundPoset.conditions` (definitions bundle `OAIQ064A003` of this split).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.OriginalRealCohenFactorization.real_factorization` and `OAI.TuringRigidity.OriginalRealDefinitionTransport.original_definition_transport` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenManyAbsorption.lean (declaration OAI.TuringRigidity.CohenManyAbsorption.same_generics_absorption)

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

namespace TuringRigidity.CohenManyAbsorption
open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem same_generics_absorption (M q A a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q) (hA : A ∈ M) (ha : a ∈ M)
    (hBA : ZFSet.prod {a} ZFSet.omega ⊆ A)
    (G : GenericFilter (Conditions q)) (hG : AtomicForcing.GroundGeneric M G)
    (L : GenericFilter (Conditions (conditions A)))
    (hL : AtomicForcing.GroundGeneric (genericExtensionSet M q G.carrier) L) :
    ∃ U : GenericFilter (Conditions (conditions A)), AtomicForcing.GroundGeneric M U ∧
      genericExtensionSet M (conditions A) U.carrier =
        genericExtensionSet (genericExtensionSet M q G.carrier) (conditions A) L.carrier := by
  sorry

end TuringRigidity.CohenManyAbsorption

end OAI
end
