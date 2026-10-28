-- Prove2me | Theorems.Thm_OAI_TuringRigidity_IteratedGenericCommonIdeal_ideal_of_iterated_generics
-- name    : OAI.TuringRigidity.IteratedGenericCommonIdeal.ideal_of_iterated_generics
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:41:02.439376+00:00
-- url     : https://prove2.me/theorems/7ddc733a-0bbf-4438-8653-dda0c87ed3b5
-- title:
--   OAI.TuringRigidity.IteratedGenericCommonIdeal.ideal_of_iterated_generics: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.IteratedGenericCommonIdeal.ideal_of_iterated_generics` of [lean/OAI/Computability/DegreeRigidity/Representation/IteratedGenericCommonIdeal.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/IteratedGenericCommonIdeal.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.IteratedGenericCommonIdeal`, with `open TransitiveNameModel BoundedSetTheory InternalCohen CountableForcing AtomicForcing`, `open CohenProductSplitting CohenBorelForcing InternalCommonRequirements`):
--
--   ```lean
--   theorem ideal_of_iterated_generics (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
--       (A : Oracle) (hA : A ∈ modelReals M) (L R : Oracle)
--       (hL : GroundGeneric M (pushFilter (realFilter L)))
--       (hR : GroundGeneric (genericExtensionSet M conditions (pushFilter (realFilter L)).carrier)
--         (pushFilter (realFilter R))) :
--       ∀ b : Degree, b ≤ degree A ↔ b ≤ degree (join A L) ∧ b ≤ degree (join A R)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.join`, `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` and `OAI.TuringRigidity.CountableForcing.GenericFilter` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenBorelForcing.realFilter` and `OAI.TuringRigidity.InternalCohen.conditions` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.BoundedSetTheory.modelReals` and `OAI.TuringRigidity.InternalCohen.pushFilter` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.RealHullGenericTriple.exists_generic_prefix_triple` and `OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/IteratedGenericCommonIdeal.lean (declaration OAI.TuringRigidity.IteratedGenericCommonIdeal.ideal_of_iterated_generics)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A006

section

attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IteratedGenericCommonIdeal
open TransitiveNameModel BoundedSetTheory InternalCohen CountableForcing AtomicForcing
open CohenProductSplitting CohenBorelForcing InternalCommonRequirements
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem ideal_of_iterated_generics (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : A ∈ modelReals M) (L R : Oracle)
    (hL : GroundGeneric M (pushFilter (realFilter L)))
    (hR : GroundGeneric (genericExtensionSet M conditions (pushFilter (realFilter L)).carrier)
      (pushFilter (realFilter R))) :
    ∀ b : Degree, b ≤ degree A ↔ b ≤ degree (join A L) ∧ b ≤ degree (join A R) := by
  sorry

end TuringRigidity.IteratedGenericCommonIdeal

end OAI
end
