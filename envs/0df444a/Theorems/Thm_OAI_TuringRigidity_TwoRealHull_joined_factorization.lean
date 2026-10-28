-- Prove2me | Theorems.Thm_OAI_TuringRigidity_TwoRealHull_joined_factorization
-- name    : OAI.TuringRigidity.TwoRealHull.joined_factorization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:48:02.303424+00:00
-- url     : https://prove2.me/theorems/d6d4be30-69bc-4940-8c58-5bce6744493e
-- title:
--   OAI.TuringRigidity.TwoRealHull.joined_factorization: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.TwoRealHull.joined_factorization` of [lean/OAI/Computability/DegreeRigidity/SetModels/TwoRealHull.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/TwoRealHull.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.TwoRealHull`, with `open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing`, `open RealGeneratedModel CohenColumnRealName InternalCountableOrdinals`):
--
--   ```lean
--   theorem joined_factorization (M K : ZFSet.{0})
--       (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
--       (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
--       (X Y : Oracle)
--       (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
--       (hY : realCode Y ∈ genericExtensionSet M (poset K) G.carrier) :
--       let N := RealGeneratedModel.hull M (realCode X)
--       let H := RealGeneratedModel.hull N (realCode Y)
--       Contains M (realCode X) N ∧ Contains N (realCode Y) H ∧
--         ∃ U : GenericFilter (Conditions (poset K)), GroundGeneric H U ∧
--           genericExtensionSet H (poset K) U.carrier = genericExtensionSet M (poset K) G.carrier
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet` and `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.InternalCountableOrdinals.FirstUncountable` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` and `OAI.TuringRigidity.BoundedSetTheory.realCode` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenColumnRealName.poset` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RealGeneratedModel.Contains` and `OAI.TuringRigidity.RealGeneratedModel.hull` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.RealHullIteration.exists_iterated_pair` and `OAI.TuringRigidity.RelativeConstructible.real_hull_generic_column_realizes` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/TwoRealHull.lean (declaration OAI.TuringRigidity.TwoRealHull.joined_factorization)

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

namespace TuringRigidity.TwoRealHull
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RealGeneratedModel CohenColumnRealName InternalCountableOrdinals
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem joined_factorization (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X Y : Oracle)
    (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hY : realCode Y ∈ genericExtensionSet M (poset K) G.carrier) :
    let N := RealGeneratedModel.hull M (realCode X)
    let H := RealGeneratedModel.hull N (realCode Y)
    Contains M (realCode X) N ∧ Contains N (realCode Y) H ∧
      ∃ U : GenericFilter (Conditions (poset K)), GroundGeneric H U ∧
        genericExtensionSet H (poset K) U.carrier = genericExtensionSet M (poset K) G.carrier := by
  sorry

end TuringRigidity.TwoRealHull

end OAI
end
