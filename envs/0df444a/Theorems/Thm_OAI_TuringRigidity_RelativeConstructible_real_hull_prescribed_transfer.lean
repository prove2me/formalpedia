-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_real_hull_prescribed_transfer
-- name    : OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:46:31.598048+00:00
-- url     : https://prove2.me/theorems/d9ef213b-6433-4196-a505-899bb9c5627d
-- title:
--   OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer` of [lean/OAI/Computability/DegreeRigidity/Representation/RealHullPrescribedTruth.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/RealHullPrescribedTruth.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing`, `open CohenColumnRealName InternalCountableOrdinals GenericIdentity`):
--
--   ```lean
--   theorem real_hull_prescribed_transfer (M K a : ZFSet.{0})
--       (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
--       (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
--       (X : Oracle) (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
--       (π : Degree ≃o Degree) (p : OracleCode) (P : Oracle)
--       (hP : realCode P ∈ RealGeneratedModel.hull M (realCode X))
--       (hsem : ∀ H : GenericFilter (Conditions (poset K)),
--         GroundGeneric (RealGeneratedModel.hull M (realCode X)) H →
--         genericExtensionSet (RealGeneratedModel.hull M (realCode X)) (poset K) H.carrier =
--           genericExtensionSet M (poset K) G.carrier →
--         ∀ A : Oracle, (realName K a).val H.carrier = realCode A → RepresentsAt π p P A) :
--       (∀ s : List Bool, ∃ H : Oracle,
--         ArithmeticPrefixForcing.Generic (fun _ => P) H ∧
--         ShuffleRequirements.Realizes s H ∧ SourceEquation p P (GenericTruth.triple H)) ∧
--       (∀ H : Oracle, ArithmeticPrefixForcing.Generic (fun _ => P) H →
--         SourceEquation p P (GenericTruth.triple H)) ∧
--       (∃ D : ArithmeticPrefixForcing.PrefixPredicate, ArithmeticPrefixForcing.ArithmeticPrefix D ∧
--         (∀ n, FiniteShuffle.DenseOpen (D (fun _ => P) n)) ∧
--         ∀ H : Oracle, ShuffleRequirements.GenericFor (D (fun _ => P)) H →
--           SourceEquation p P (GenericTruth.triple H)) ∧
--       ∀ Y : Oracle, realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
--         ArithmeticPrefixForcing.Generic (fun _ => P) Y → RepresentsAt π p P Y
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.OracleCode`, `OAI.TuringRigidity.ArithmeticPrefixForcing.ArithmeticPrefix`, `OAI.TuringRigidity.ArithmeticPrefixForcing.Generic`, `OAI.TuringRigidity.ArithmeticPrefixForcing.PrefixPredicate`, `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.FiniteShuffle.DenseOpen`, `OAI.TuringRigidity.GenericTruth.triple`, `OAI.TuringRigidity.ShuffleRequirements.Realizes`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` and `OAI.TuringRigidity.RecursiveNames.Name.val` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.InternalCountableOrdinals.FirstUncountable` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` and `OAI.TuringRigidity.BoundedSetTheory.realCode` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.GenericIdentity.RepresentsAt` and `OAI.TuringRigidity.ShuffleRequirements.GenericFor` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.CohenColumnRealName.poset`, `OAI.TuringRigidity.CohenColumnRealName.realName` and `OAI.TuringRigidity.GenericIdentity.SourceEquation` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RealGeneratedModel.hull` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.global_arithmetic_generic_program` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/RealHullPrescribedTruth.lean (declaration OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer)

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

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals GenericIdentity
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem real_hull_prescribed_transfer (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X : Oracle) (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (π : Degree ≃o Degree) (p : OracleCode) (P : Oracle)
    (hP : realCode P ∈ RealGeneratedModel.hull M (realCode X))
    (hsem : ∀ H : GenericFilter (Conditions (poset K)),
      GroundGeneric (RealGeneratedModel.hull M (realCode X)) H →
      genericExtensionSet (RealGeneratedModel.hull M (realCode X)) (poset K) H.carrier =
        genericExtensionSet M (poset K) G.carrier →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A → RepresentsAt π p P A) :
    (∀ s : List Bool, ∃ H : Oracle,
      ArithmeticPrefixForcing.Generic (fun _ => P) H ∧
      ShuffleRequirements.Realizes s H ∧ SourceEquation p P (GenericTruth.triple H)) ∧
    (∀ H : Oracle, ArithmeticPrefixForcing.Generic (fun _ => P) H →
      SourceEquation p P (GenericTruth.triple H)) ∧
    (∃ D : ArithmeticPrefixForcing.PrefixPredicate, ArithmeticPrefixForcing.ArithmeticPrefix D ∧
      (∀ n, FiniteShuffle.DenseOpen (D (fun _ => P) n)) ∧
      ∀ H : Oracle, ShuffleRequirements.GenericFor (D (fun _ => P)) H →
        SourceEquation p P (GenericTruth.triple H)) ∧
    ∀ Y : Oracle, realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
      ArithmeticPrefixForcing.Generic (fun _ => P) Y → RepresentsAt π p P Y := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
