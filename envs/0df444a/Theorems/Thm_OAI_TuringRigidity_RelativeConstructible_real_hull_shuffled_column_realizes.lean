-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_real_hull_shuffled_column_realizes
-- name    : OAI.TuringRigidity.RelativeConstructible.real_hull_shuffled_column_realizes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:53:27.915282+00:00
-- url     : https://prove2.me/theorems/ce700a2d-068f-40f5-ba17-911290bb4319
-- title:
--   OAI.TuringRigidity.RelativeConstructible.real_hull_shuffled_column_realizes: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.real_hull_shuffled_column_realizes` of [lean/OAI/Computability/DegreeRigidity/Representation/RealHullColumnRealization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/RealHullColumnRealization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open TransitiveNameModel BoundedSetTheory CountableForcing InternalCountableOrdinals`, `open CohenColumnRealName`):
--
--   ```lean
--   theorem real_hull_shuffled_column_realizes (M K a : ZFSet.{0})
--       (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
--       (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
--       (X Y L : Oracle)
--       (hXE : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
--       (hYE : realCode Y ∈ genericExtensionSet M (poset K) G.carrier)
--       (hLE : realCode L ∈ genericExtensionSet M (poset K) G.carrier)
--       (hL : AtomicForcing.GroundGeneric (RealGeneratedModel.hull M (realCode X))
--         (InternalCohen.pushFilter (CohenBorelForcing.realFilter L))) :
--       ColumnRealizesExtension (RealGeneratedModel.hull M (realCode X)) K a
--         (genericExtensionSet M (poset K) G.carrier) (GenericCoding.code Y L)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet` and `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.InternalCountableOrdinals.FirstUncountable` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` and `OAI.TuringRigidity.BoundedSetTheory.realCode` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenBorelForcing.realFilter` and `OAI.TuringRigidity.InternalCohen.conditions` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.CohenColumnRealName.poset`, `OAI.TuringRigidity.GenericCoding.code` and `OAI.TuringRigidity.InternalCohen.pushFilter` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RealGeneratedModel.hull` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.RelativeConstructible.ColumnRealizesExtension` (definitions bundle `OAIQ064A008` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/RealHullColumnRealization.lean (declaration OAI.TuringRigidity.RelativeConstructible.real_hull_shuffled_column_realizes)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008

section

attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing InternalCountableOrdinals
open CohenColumnRealName
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem real_hull_shuffled_column_realizes (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (X Y L : Oracle)
    (hXE : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hYE : realCode Y ∈ genericExtensionSet M (poset K) G.carrier)
    (hLE : realCode L ∈ genericExtensionSet M (poset K) G.carrier)
    (hL : AtomicForcing.GroundGeneric (RealGeneratedModel.hull M (realCode X))
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter L))) :
    ColumnRealizesExtension (RealGeneratedModel.hull M (realCode X)) K a
      (genericExtensionSet M (poset K) G.carrier) (GenericCoding.code Y L) := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
