-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_support_prepared_strengthening
-- name    : OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_support_prepared_strengthening
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:15:22.256584+00:00
-- url     : https://prove2.me/theorems/de437976-75c0-4d4f-b41e-0e5f1637632c
-- title:
--   OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_support_prepared_strengthening: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_support_prepared_strengthening` of [lean/OAI/SetTheory/PartitionPrinciple/Forcing/GroundMainFinalStructuralSupportPreparation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Forcing/GroundMainFinalStructuralSupportPreparation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment`, with `open SetFormula SetRealization`, `open scoped ZFSet`):
--
--   ```lean
--   theorem structural_support_prepared_strengthening
--       (collection : CollectionSchema M.sets)
--       (infinite : Realize M.sets infinity Fin.elim0)
--       (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
--       (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
--       (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
--       {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
--     let geometry := run.finalGeometry i₀
--     letI := geometry.group_code.toGroup
--     letI := geometry.meet.order.toPartialOrder
--     letI := geometry.decodedBottom
--     let s := SetMembers.presentation geometry.carrier
--     let b := SetMembers.presentation geometry.actors
--     let a := geometry.decodedAction
--     let directed := geometry.decoded_directed fulfilled.directed
--     let hL := geometry.carrier_ground
--     let hG := geometry.actors_ground
--     let hC := hColumns
--     let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
--     letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
--     letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
--       ⟨s.carrier, hL⟩
--     let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
--     let c := SetMembers.presentation (M.smallPartialFunctions
--       (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
--     let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
--     let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
--     let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
--     ∀ valid : ∀ z ∈ T, IsName c z,
--     let lifted := Name.renamedFamily c.pairEmpty id T valid
--     let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
--     ∀ (_hLifted : lifted ∈ M.sets) (_hSquared : squared ∈ M.sets)
--       (_valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
--       (_valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
--       (_closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
--       (_closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
--       (_children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
--         HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
--       (_children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
--         HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
--       (stages history : ZFSet.{u}) (_hs : stages ∈ M.sets) (_hh : history ∈ M.sets)
--       (_stagesOrdinal : ordinalSetProperty stages)
--       (_trace : OrdinalRecursionTrace (fun level prior stage => stage =
--         M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
--           b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
--           (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
--     let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
--       (supportBasisCode s b a.principalFix) lifted squared stages history
--     let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
--     ∀ p ∈ upperQ,
--       GroundSupportPreparedStrengtheningResult M c lifted stages packed s.carrier p
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.Forcing.natSetCode`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Forcing.GroupCode.toGroup`, `OAI.PartitionPilot.Forcing.MeetOrderCode`, `OAI.PartitionPilot.Forcing.PartialOrderCode.toPartialOrder`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallFunctionOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallFunctionTop`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallPartialFunctions` and `OAI.PartitionPilot.SetRealization.SetMembers.presentation` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.orderedPairNameFamily` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry`, `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decodedBottom`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.TransitiveGround.rowPositionSequences`, `OAI.PartitionPilot.SetRealization.Presentation.nonbottom` and `OAI.PartitionPilot.SetRealization.Presentation.pairEmpty` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.rowTupleTerms`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decodedAction`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decoded_action_eq`, `OAI.PartitionPilot.Forcing.Name.renamedFamily`, `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowNameGraph` and `OAI.PartitionPilot.Forcing.TransitiveGround.internalRowAction` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel`, `OAI.PartitionPilot.Forcing.GroundMainPrefix` and `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decoded_directed` (definitions bundle `OAIQ253P006` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing` and `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.GroundSupportPreparedStrengtheningResult` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.finalGeometry`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStage`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory` and `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet`, `OAI.PartitionPilot.Forcing.SetFormula.union` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundEmbeddable` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proofs of `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_lifted_rows_not_wellorderable_not_choice`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_ordinal_choice` and `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.successor_prepared_insertion_profiles` of this split import it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Forcing/GroundMainFinalStructuralSupportPreparation.lean (declaration OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_support_prepared_strengthening)

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
open scoped ZFSet
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem structural_support_prepared_strengthening
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (_hLifted : lifted ∈ M.sets) (_hSquared : squared ∈ M.sets)
    (_valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (_valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (_closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (_closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (_children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (_children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (_hs : stages ∈ M.sets) (_hh : history ∈ M.sets)
    (_stagesOrdinal : ordinalSetProperty stages)
    (_trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  ∀ p ∈ upperQ,
    GroundSupportPreparedStrengtheningResult M c lifted stages packed s.carrier p := by
  sorry

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end
