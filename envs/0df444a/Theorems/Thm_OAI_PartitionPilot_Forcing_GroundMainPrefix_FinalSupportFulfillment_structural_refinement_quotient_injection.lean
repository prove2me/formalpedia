-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_refinement_quotient_injection
-- name    : OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_refinement_quotient_injection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:20:32.339694+00:00
-- url     : https://prove2.me/theorems/e245acac-33e7-41de-846b-3e5e04aabb65
-- title:
--   OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_refinement_quotient_injection: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_refinement_quotient_injection` of [lean/OAI/SetTheory/PartitionPrinciple/Models/GroundMainFinalPartitionModel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Models/GroundMainFinalPartitionModel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment`, with `open scoped ZFSet`, `open SetFormula SetRealization`):
--
--   ```lean
--   theorem structural_refinement_quotient_injection
--       (collection : CollectionSchema M.sets)
--       (infinite : Realize M.sets infinity Fin.elim0)
--       (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
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
--     let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
--     let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
--     let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
--       collection hL hG graph
--     let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
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
--     ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
--       (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
--       (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
--       (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
--       (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
--       (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
--         HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
--       (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
--         HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
--       (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
--       (stagesOrdinal : ordinalSetProperty stages)
--       (trace : OrdinalRecursionTrace (fun level prior stage => stage =
--         M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
--           b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
--           (supportBasisCode s b a.principalFix) lifted squared level prior) stages history)
--       (_standard : GroundStandardInaccessible M stages)
--       (_smallRows : GroundBelow M c.carrier stages) (_smallLifted : GroundBelow M lifted stages),
--     let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
--     let two := M.natSetCode_mem separation infinite 2
--     let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
--     let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
--     let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
--     let omega := M.omega_mem separation infinite
--     let topMem := c.encode_mem ⊤
--     let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
--       fun r hr => by
--         obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
--         exact (c.pair_mem_conditionOrder r ⊤).2 le_top
--     let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
--       (supportBasisCode s b a.principalFix) lifted squared stages history
--     let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
--       (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
--       (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
--     let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
--     letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
--     letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
--       historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
--     let upper := SetMembers.presentation upperSet
--     let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
--       pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
--       nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
--       topMem topRows hs hh stagesOrdinal trace
--     let validUpper := M.refinementHistoryRowNameFamily_valid c historyRun.carriers stagesOrdinal carrier lifted valid1
--     ∀ (H : ConditionFilter (SetMembers upperSet)),
--       H.GenericFor (formulaFamily (M.nameDomain upper)) →
--       (∀ (beta : ZFSet.{u}) (member : beta ∈ stages),
--         let hBeta := M.transitive hs member
--         let betaOrdinal := ordinalSetProperty_member stagesOrdinal member
--         let betaSubset := (And.left stagesOrdinal) beta member
--         let lowerPacked := graphRestriction beta packed
--         let lowerSet := M.refinementHistoryForcing c.carrier lifted beta lowerPacked
--         letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted beta lowerPacked
--         letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted beta lowerPacked
--           (historyRun.carriers.restrict betaOrdinal betaSubset) betaOrdinal carrier (c.encode ⊤) topMem topRows
--         let lower := SetMembers.presentation lowerSet
--         let projection := M.semanticStructuralTrace_completeProjection c act b s a ⊥ directed lifted squared (c.encode ⊤)
--           pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
--           nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
--           topMem topRows hs hh stagesOrdinal trace beta hBeta betaOrdinal betaSubset infinite choice
--         (projection.projectedFilter H).GenericFor (M.codedFamily lower) ∧
--         (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower))) →
--       ∀ tau : Fin 3 → (M.nameDomain upper).names,
--         (∀ i, HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) (tau i).val) →
--         RefinementValidityCode
--           (Name.eval {p | H.mem p} (Name.familySet ⊤ lifted validUpper))
--           (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
--           (Name.eval {p | H.mem p} (tau 2).val) →
--         ∃ J ∈ (M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H).sets,
--           InjectionCode
--             (equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
--               (Name.eval {p | H.mem p} (tau 2).val))
--             (equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
--               (Name.eval {p | H.mem p} (tau 1).val)) J
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.Forcing.natSetCode`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Forcing.GroupCode.toGroup`, `OAI.PartitionPilot.Forcing.MeetOrderCode`, `OAI.PartitionPilot.Forcing.PartialOrderCode.toPartialOrder`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.natSetCode_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.omega_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.prod_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallFunctionOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallFunctionTop`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallPartialFunctions`, `OAI.PartitionPilot.SetRealization.Presentation.encode_mem` and `OAI.PartitionPilot.SetRealization.SetMembers.presentation` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.CompleteProjection`, `OAI.PartitionPilot.Forcing.ConditionFilter`, `OAI.PartitionPilot.Forcing.RefinementValidityCode`, `OAI.PartitionPilot.Forcing.equivalenceClasses`, `OAI.PartitionPilot.Forcing.graphRestriction`, `OAI.PartitionPilot.Forcing.orderedPairNameFamily`, `OAI.PartitionPilot.Forcing.ordinalSetProperty_member`, `OAI.PartitionPilot.Forcing.CompleteProjection.projectedFilter` and `OAI.PartitionPilot.Forcing.ConditionFilter.GenericFor` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.refinementFormulaDataCode`, `OAI.PartitionPilot.Forcing.stageOneRawTests`, `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix`, `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` and `OAI.PartitionPilot.SetRealization.Presentation.pair_mem_conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry`, `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace`, `OAI.PartitionPilot.Forcing.forcingStageCode`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decodedBottom`, `OAI.PartitionPilot.Forcing.Name.eval`, `OAI.PartitionPilot.Forcing.Name.familySet`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.PosetAction.conditionMapFamily`, `OAI.PartitionPilot.Forcing.SetFormula.formulaFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.codedFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.nameDomain`, `OAI.PartitionPilot.Forcing.TransitiveGround.nonbottom_carrier_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.rowPositionSequences`, `OAI.PartitionPilot.Forcing.TransitiveGround.symmetricExtension`, `OAI.PartitionPilot.SetRealization.Presentation.nonbottom`, `OAI.PartitionPilot.SetRealization.Presentation.pairEmpty` and `OAI.PartitionPilot.Forcing.Name.NameDomain` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.rowTupleTerms`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decodedAction`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decoded_action_eq`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decoded_order_eq`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decoded_supportBasis_ground`, `OAI.PartitionPilot.Forcing.Name.renamedFamily`, `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowNameGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.countableFunctionOrder_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.countablePartialFunctions_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.internalRowAction`, `OAI.PartitionPilot.Forcing.TransitiveGround.internalRowActionGraph_mem` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder_code` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel`, `OAI.PartitionPilot.Forcing.GroundMainPrefix` and `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decoded_directed` (definitions bundle `OAIQ253P006` of this split); `OAI.PartitionPilot.Forcing.RawRefinementStageWitness`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory.inclusion`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory.restriction`, `OAI.PartitionPilot.Forcing.TransitiveGround.conditionMapFamily_mem_of_actionGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryOrderTop` and `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryPartialOrder` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.finalGeometry`, `OAI.PartitionPilot.Forcing.TransitiveGround.groundOmegaOne`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryRowNameFamily_valid`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStage`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingTrace_recursiveOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingTrace_witnesses`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory_mem` and `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAction`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_completeProjection` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralHistory_rawTests_mono` (definitions bundle `OAIQ253P011` of this split); `OAI.PartitionPilot.Forcing.GroundBelow`, `OAI.PartitionPilot.Forcing.GroundStandardInaccessible`, `OAI.PartitionPilot.Forcing.InjectionCode`, `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.setTransitive`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet`, `OAI.PartitionPilot.Forcing.SetFormula.union` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundEmbeddable` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_rowSemanticQuotientInjectionModel` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Models/GroundMainFinalPartitionModel.lean (declaration OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_refinement_quotient_injection)

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
import Definitions.Def_OAIQ253P011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem structural_refinement_quotient_injection
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
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
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
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
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history)
    (_standard : GroundStandardInaccessible M stages)
    (_smallRows : GroundBelow M c.carrier stages) (_smallLifted : GroundBelow M lifted stages),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  let upper := SetMembers.presentation upperSet
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let validUpper := M.refinementHistoryRowNameFamily_valid c historyRun.carriers stagesOrdinal carrier lifted valid1
  ∀ (H : ConditionFilter (SetMembers upperSet)),
    H.GenericFor (formulaFamily (M.nameDomain upper)) →
    (∀ (beta : ZFSet.{u}) (member : beta ∈ stages),
      let hBeta := M.transitive hs member
      let betaOrdinal := ordinalSetProperty_member stagesOrdinal member
      let betaSubset := (And.left stagesOrdinal) beta member
      let lowerPacked := graphRestriction beta packed
      let lowerSet := M.refinementHistoryForcing c.carrier lifted beta lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted beta lowerPacked
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted beta lowerPacked
        (historyRun.carriers.restrict betaOrdinal betaSubset) betaOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation lowerSet
      let projection := M.semanticStructuralTrace_completeProjection c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hs hh stagesOrdinal trace beta hBeta betaOrdinal betaSubset infinite choice
      (projection.projectedFilter H).GenericFor (M.codedFamily lower) ∧
      (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower))) →
    ∀ tau : Fin 3 → (M.nameDomain upper).names,
      (∀ i, HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) (tau i).val) →
      RefinementValidityCode
        (Name.eval {p | H.mem p} (Name.familySet ⊤ lifted validUpper))
        (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
        (Name.eval {p | H.mem p} (tau 2).val) →
      ∃ J ∈ (M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H).sets,
        InjectionCode
          (equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 2).val))
          (equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 1).val)) J := by
  sorry

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end
