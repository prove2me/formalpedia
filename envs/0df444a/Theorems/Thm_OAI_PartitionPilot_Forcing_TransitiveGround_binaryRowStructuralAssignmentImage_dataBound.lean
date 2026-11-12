-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_binaryRowStructuralAssignmentImage_dataBound
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowStructuralAssignmentImage_dataBound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:07:35.614472+00:00
-- url     : https://prove2.me/theorems/4a99187e-3e54-4c83-98be-642118f070d5
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowStructuralAssignmentImage_dataBound: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowStructuralAssignmentImage_dataBound` of [lean/OAI/SetTheory/PartitionPrinciple/Forcing/GroundBinaryRowStructuralDataBoundActions.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Forcing/GroundBinaryRowStructuralDataBoundActions.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open scoped ZFSet`, `open SetRealization SetFormula`):
--
--   ```lean
--   theorem binaryRowStructuralAssignmentImage_dataBound {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
--       (muOrdinal : ordinalSetProperty mu) :
--       letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
--       letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
--         ⟨s.carrier, hL⟩
--       let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
--       let c := SetMembers.presentation (M.smallPartialFunctions
--         (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
--       let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
--       let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
--       let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
--       ∀ valid : ∀ z ∈ T, IsName c z,
--       let lifted := Name.renamedFamily c.pairEmpty id T valid
--       let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
--       let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
--       ∀ (_hLifted : lifted ∈ M.sets) (_hSquared : squared ∈ M.sets)
--         (_valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
--         (_valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
--         (_closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
--         (_closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
--         (_children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
--           HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
--         (_children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
--           HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
--         (stages history : ZFSet.{u}) (_hs : stages ∈ M.sets) (_hh : history ∈ M.sets)
--         (_stagesOrdinal : ordinalSetProperty stages)
--         (_trace : OrdinalRecursionTrace (fun level prior stage => stage =
--           M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
--             b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
--             (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
--       let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
--       let two := M.natSetCode_mem separation infinite 2
--       let _carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
--       let _forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
--       let _forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
--       let _omega := M.omega_mem separation infinite
--       let _topMem := c.encode_mem ⊤
--       let _topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
--         fun r hr => by
--           obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
--           exact (c.pair_mem_conditionOrder r ⊤).2 le_top
--       let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
--         (supportBasisCode s b a.principalFix) lifted squared stages history
--       let I := refinementDataHistoryIndices stages packed
--       let anchors := refinementIndexFieldGraph I s.carrier 2
--       ∀ (g : G) (D : L) (A : ZFSet.{u}), A ∈ M.sets →
--         (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈ stageOneDataBounds A I lifted S s.carrier mu
--           s.nonbottom.carrier s.conditionOrder anchors tuples) →
--       let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
--         (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode g) A
--       movedA ∈ M.sets ∧
--         stageOneDataBounds movedA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples ∈ M.sets ∧
--         ∀ z ∈ movedA, ZFSet.pair z (s.encode (a.iso g D)) ∈
--           stageOneDataBounds movedA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.Forcing.natSetCode`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.natSetCode_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.omega_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.prod_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallFunctionOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallFunctionTop`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallPartialFunctions`, `OAI.PartitionPilot.SetRealization.Presentation.encode_mem` and `OAI.PartitionPilot.SetRealization.SetMembers.presentation` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.orderedPairNameFamily` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.refinementDataHistoryIndices`, `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix`, `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` and `OAI.PartitionPilot.SetRealization.Presentation.pair_mem_conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace`, `OAI.PartitionPilot.Forcing.refinementIndexFieldGraph`, `OAI.PartitionPilot.Forcing.stageOneDataBounds`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.PosetAction.conditionMapFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.nonbottom_carrier_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.rowPositionSequences`, `OAI.PartitionPilot.SetRealization.Presentation.nonbottom` and `OAI.PartitionPilot.SetRealization.Presentation.pairEmpty` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.liftedRowTupleFamily`, `OAI.PartitionPilot.Forcing.rowTupleTerms`, `OAI.PartitionPilot.Forcing.Name.renamedFamily`, `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowNameGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.countableFunctionOrder_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.countablePartialFunctions_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.internalRowAction` and `OAI.PartitionPilot.Forcing.TransitiveGround.internalRowActionGraph_mem` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.structuralAssignmentImage`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStage` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet` and `OAI.PartitionPilot.Forcing.SetFormula.union` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proofs of `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_compatible_insertion_unions`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_dense_mixture_equalities` and `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_lifted_rows_not_wellorderable_not_choice` of this split import it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Forcing/GroundBinaryRowStructuralDataBoundActions.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowStructuralAssignmentImage_dataBound)

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

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

include collection order nodeMaps supports

theorem binaryRowStructuralAssignmentImage_dataBound {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (muOrdinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
    let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
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
    let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
    let two := M.natSetCode_mem separation infinite 2
    let _carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    let _forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    let _forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
    let _omega := M.omega_mem separation infinite
    let _topMem := c.encode_mem ⊤
    let _topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared stages history
    let I := refinementDataHistoryIndices stages packed
    let anchors := refinementIndexFieldGraph I s.carrier 2
    ∀ (g : G) (D : L) (A : ZFSet.{u}), A ∈ M.sets →
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈ stageOneDataBounds A I lifted S s.carrier mu
        s.nonbottom.carrier s.conditionOrder anchors tuples) →
    let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode g) A
    movedA ∈ M.sets ∧
      stageOneDataBounds movedA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples ∈ M.sets ∧
      ∀ z ∈ movedA, ZFSet.pair z (s.encode (a.iso g D)) ∈
        stageOneDataBounds movedA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples := by
  sorry

end PartitionPilot.Forcing.TransitiveGround

end OAI
end
