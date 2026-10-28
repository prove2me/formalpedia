-- Prove2me | Theorems.Thm_OAI_TuringRigidity_CohenDisjointPrefixPair_exists_iterated_pair
-- name    : OAI.TuringRigidity.CohenDisjointPrefixPair.exists_iterated_pair
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:39:15.65649+00:00
-- url     : https://prove2.me/theorems/e8c5dabe-eebf-4dcb-90c2-ed977df4f574
-- title:
--   OAI.TuringRigidity.CohenDisjointPrefixPair.exists_iterated_pair: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.CohenDisjointPrefixPair.exists_iterated_pair` of [lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenDisjointPrefixPair.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenDisjointPrefixPair.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.CohenDisjointPrefixPair`, with `open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing`, `open CohenColumnRealName InternalCohenProjectedGeneric`):
--
--   ```lean
--   theorem exists_iterated_pair (M K a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
--       (hK : K ∈ M) (ha : a ∈ K) (hb : b ∈ K) (hab : b ≠ a)
--       (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G) :
--       ∃ L R : Oracle,
--         realCode L ∈ genericExtensionSet M (poset K) G.carrier ∧
--         realCode R ∈ genericExtensionSet M (poset K) G.carrier ∧
--         GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) ∧
--         GroundGeneric (genericExtensionSet M InternalCohen.conditions
--           (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)).carrier)
--           (InternalCohen.pushFilter (CohenBorelForcing.realFilter R))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet` and `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` and `OAI.TuringRigidity.BoundedSetTheory.realCode` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenBorelForcing.realFilter` and `OAI.TuringRigidity.InternalCohen.conditions` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.CohenColumnRealName.poset` and `OAI.TuringRigidity.InternalCohen.pushFilter` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RealHullIteration.exists_iterated_pair` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenDisjointPrefixPair.lean (declaration OAI.TuringRigidity.CohenDisjointPrefixPair.exists_iterated_pair)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A006

section

attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenDisjointPrefixPair
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem exists_iterated_pair (M K a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K) (hb : b ∈ K) (hab : b ≠ a)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G) :
    ∃ L R : Oracle,
      realCode L ∈ genericExtensionSet M (poset K) G.carrier ∧
      realCode R ∈ genericExtensionSet M (poset K) G.carrier ∧
      GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) ∧
      GroundGeneric (genericExtensionSet M InternalCohen.conditions
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)).carrier)
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) := by
  sorry

end TuringRigidity.CohenDisjointPrefixPair

end OAI
end
