-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RealHullIteration_exists_iterated_prefix_pair
-- name    : OAI.TuringRigidity.RealHullIteration.exists_iterated_prefix_pair
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:43:51.422668+00:00
-- url     : https://prove2.me/theorems/f08d6c12-891d-417c-a84c-e786ffb3d6b0
-- title:
--   OAI.TuringRigidity.RealHullIteration.exists_iterated_prefix_pair: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RealHullIteration.exists_iterated_prefix_pair` of [lean/OAI/Computability/DegreeRigidity/Representation/RealHullIteration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/RealHullIteration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RealHullIteration`, with `open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing`, `open CohenColumnRealName InternalCountableOrdinals RealGeneratedModel`):
--
--   ```lean
--   theorem exists_iterated_prefix_pair (M K : ZFSet.{0})
--       (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
--       (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
--       (X Y : Oracle)
--       (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
--       (hY : realCode Y ∈ genericExtensionSet M (poset K) G.carrier) (s t : List Bool) :
--       let N := RealGeneratedModel.hull M (realCode X)
--       let H := RealGeneratedModel.hull N (realCode Y)
--       Contains M (realCode X) N ∧ Contains N (realCode Y) H ∧ ∃ L R : Oracle,
--         realCode L ∈ genericExtensionSet M (poset K) G.carrier ∧
--         realCode R ∈ genericExtensionSet M (poset K) G.carrier ∧
--         GroundGeneric H (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) ∧
--         GroundGeneric (genericExtensionSet H InternalCohen.conditions
--           (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)).carrier)
--           (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) ∧
--         ShuffleRequirements.Realizes s L ∧ ShuffleRequirements.Realizes t R
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.ShuffleRequirements.Realizes`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet` and `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.InternalCountableOrdinals.FirstUncountable` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` and `OAI.TuringRigidity.BoundedSetTheory.realCode` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenBorelForcing.realFilter` and `OAI.TuringRigidity.InternalCohen.conditions` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.CohenColumnRealName.poset` and `OAI.TuringRigidity.InternalCohen.pushFilter` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RealGeneratedModel.Contains` and `OAI.TuringRigidity.RealGeneratedModel.hull` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RealHullGenericTriple.exists_generic_prefix_triple` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/RealHullIteration.lean (declaration OAI.TuringRigidity.RealHullIteration.exists_iterated_prefix_pair)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A006
import Definitions.Def_OAIQ064A007

section

attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RealHullIteration
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals RealGeneratedModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem exists_iterated_prefix_pair (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X Y : Oracle)
    (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hY : realCode Y ∈ genericExtensionSet M (poset K) G.carrier) (s t : List Bool) :
    let N := RealGeneratedModel.hull M (realCode X)
    let H := RealGeneratedModel.hull N (realCode Y)
    Contains M (realCode X) N ∧ Contains N (realCode Y) H ∧ ∃ L R : Oracle,
      realCode L ∈ genericExtensionSet M (poset K) G.carrier ∧
      realCode R ∈ genericExtensionSet M (poset K) G.carrier ∧
      GroundGeneric H (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) ∧
      GroundGeneric (genericExtensionSet H InternalCohen.conditions
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)).carrier)
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) ∧
      ShuffleRequirements.Realizes s L ∧ ShuffleRequirements.Realizes t R := by
  sorry

end TuringRigidity.RealHullIteration

end OAI
end
