-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_exists_prefixPreparationBatch
-- name    : OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_prefixPreparationBatch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:24:51.393197+00:00
-- url     : https://prove2.me/theorems/a9c84475-2b00-4204-bdc2-11f6790b4d82
-- title:
--   OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_prefixPreparationBatch: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_prefixPreparationBatch` of [lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundMainFinalPrefixPreparationBatches.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundMainFinalPrefixPreparationBatches.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment`, with `open SetFormula SetRealization`):
--
--   ```lean
--   theorem exists_prefixPreparationBatch
--       (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
--       (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
--       (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
--       (rowClosed : InternallyCountablyClosed M c) :
--     let geometry := run.finalGeometry i₀
--     letI := geometry.group_code.toGroup
--     letI := geometry.meet.order.toPartialOrder
--     letI := geometry.decodedBottom
--     let b := SetMembers.presentation geometry.carrier
--     let t := SetMembers.presentation geometry.actors
--     let d := geometry.decodedAction
--     let directed := geometry.decoded_directed fulfilled.directed
--       ∀ (a : PosetAction (SetMembers geometry.actors) R) (T T2 rowTop : ZFSet.{u})
--         (carrier : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
--         (rowAction : a.actionGraph c t ∈ M.sets)
--         (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
--         (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
--         (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
--         (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
--         (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
--         (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
--           HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
--         (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
--           HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
--         (topMem : rowTop ∈ c.carrier)
--         (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder),
--     let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
--     let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
--     let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
--       collection geometry.carrier_ground geometry.actors_ground nodeAction
--     let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
--     let omega := M.omega_mem separation infinite
--       ∀ (stages history alpha : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
--         (ordinal : ordinalSetProperty stages)
--         (trace : OrdinalRecursionTrace (fun level prior stage => stage =
--           M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
--             t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
--             (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
--         (member : alpha ∈ stages),
--     let hAlpha := M.transitive hs member
--     let cutOrdinal := ordinalSetProperty_member ordinal member
--     let subset := (And.left ordinal) alpha member
--     let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
--       (supportBasisCode b t d.principalFix) T T2 stages history
--     let lowerPacked := graphRestriction alpha packed
--     let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
--     let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
--       (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
--       (supportBasisCode b t d.principalFix) T T2 ordinal trace
--     letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
--     letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
--       (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
--     let lower := SetMembers.presentation Q
--     let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
--       cutOrdinal carrier T valid1
--     let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
--           pairing unions powers separation collection carrier rowOrder rowAction
--           geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
--           hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
--     let inputs := M.semanticStructuralPrefix_preparation_inputs c a t b d ⊥ directed T T2 rowTop
--           pairing unions powers separation collection carrier rowOrder rowAction
--           geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
--           hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
--         infinite choice rowClosed
--     let lowerGround := inputs.1
--     let maps := inputs.2.2.1
--     let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
--       ∀ (row A : ZFSet.{u}) (_condition : ZFSet.pair row A ∈
--         M.refinementHistoryForcing c.carrier T stages packed),
--     let selected := assignmentOnIndices indices T A
--     let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
--     let bound := M.groundRelations T lower.carrier
--     let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
--       ∀ (H : ConditionFilter (SetMembers Q))
--         (_genericCoded : H.GenericFor (M.codedFamily lower))
--         (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain lower)))
--         (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
--           d.principalFix v ≤ lowerAct.stabilizer lower x.val →
--           d.principalFix w ≤ lowerAct.stabilizer lower y.val →
--           HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) x.val →
--           HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) y.val →
--           Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
--           ∃ τ : (M.nameDomain lower).names,
--             HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) τ.val ∧
--             d.principalFix (geometry.meet.smallMeet v w) ≤ lowerAct.stabilizer lower τ.val ∧
--             Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
--         (p : SetMembers Q) (_hp : H.mem p),
--         ∃ (validJ : ∀ z ∈ J, IsName lower z) (hJ : J ∈ M.sets),
--           M.groundEmbeddable J ZFSet.omega ∧
--           (∀ z : Name lower, z.val ∈ J →
--             HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) z ∧
--             Name.eval {q | H.mem q} z ⊆ Name.eval {q | H.mem q} (Name.familySet ⊤ T valid)) ∧
--         ∃ (k : ZFSet.{u}) (hk : k ∈ M.sets),
--           ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
--             (M.niceSupportNameCodes lowerAct lower T d.principalFix)) k ∧
--           k ⊆ M.supportedCertificateFamilyRelation lowerAct lower b T d.principalFix
--             geometry.order J validJ H ∧
--           ∃ q, H.mem q ∧ q ≤ p ∧
--             Forces (M.nameDomain lower) supportedCertificateFamilyFormula
--               (M.supportedCertificateFamilyEnv lowerAct lower t b T d.principalFix pairing unions powers
--                 separation collection lowerGround geometry.actors_ground geometry.carrier_ground
--                 (geometry.decoded_supportBasis_ground pairing unions powers separation)
--                 maps hT valid (M.omega_mem separation infinite) geometry.order J k
--                 geometry.order_ground hJ hk validJ) q ∧
--             ∃ enumerations ∈ M.sets,
--               ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier
--                 (M.niceSupportNameCodes lowerAct lower T d.principalFix)) enumerations ∧
--               enumerations ⊆ M.certificateEnumerationRelation J b.carrier
--                 (M.niceSupportNameCodes lowerAct lower T d.principalFix) k ∧
--               (∀ j F B f e names,
--                 ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
--                 ZFSet.pair j (ZFSet.pair e names) ∈ enumerations →
--                 SynchronizedEnumerationCode ZFSet.omega
--                   (M.niceSupportNameCodes lowerAct lower T d.principalFix) B f e names) ∧
--               ∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
--                 ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
--                 F = M.visibleSupportProfile lowerAct lower b d T H (Name.eval {p | H.mem p} z.val) ∧
--                 MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
--                 B.Nonempty ∧ M.DecidesVisibilityProfile lowerAct lower b d.principalFix T F z.val q ∧
--                 (∀ v ∈ B, ∀ tau : Name lower, tau.val ∈ M.niceSupportNameCodes lowerAct lower T d.principalFix →
--                   ZFSet.pair v tau.val ∈ f → Name.ForcesEq q z.val tau) ∧
--                 ∃ e ∈ M.sets, ∃ names ∈ M.sets,
--                   ZFSet.IsFunc ZFSet.omega B e ∧
--                   ZFSet.IsFunc ZFSet.omega (M.niceSupportNameCodes lowerAct lower T d.principalFix) names ∧
--                   (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
--                   (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
--                     ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
--                   (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
--                     ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.MeetFilterCode`, `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.Forcing.relationImage`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Forcing.GroupCode.toGroup`, `OAI.PartitionPilot.Forcing.MeetOrderCode`, `OAI.PartitionPilot.Forcing.PartialOrderCode.toPartialOrder`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.groundRelations`, `OAI.PartitionPilot.Forcing.TransitiveGround.omega_mem` and `OAI.PartitionPilot.SetRealization.SetMembers.presentation` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.ConditionFilter`, `OAI.PartitionPilot.Forcing.SynchronizedEnumerationCode`, `OAI.PartitionPilot.Forcing.graphRestriction`, `OAI.PartitionPilot.Forcing.ordinalSetProperty_member` and `OAI.PartitionPilot.Forcing.ConditionFilter.GenericFor` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.MeetOrderCode.smallMeet`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry`, `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.InternallyCountablyClosed`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace`, `OAI.PartitionPilot.Forcing.assignmentOnIndices`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decodedBottom`, `OAI.PartitionPilot.Forcing.Name.ForcesEq`, `OAI.PartitionPilot.Forcing.Name.eval`, `OAI.PartitionPilot.Forcing.Name.familySet`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.PosetAction.conditionMapFamily`, `OAI.PartitionPilot.Forcing.PosetAction.stabilizer`, `OAI.PartitionPilot.Forcing.SetFormula.Forces`, `OAI.PartitionPilot.Forcing.SetFormula.formulaFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.DecidesVisibilityProfile`, `OAI.PartitionPilot.Forcing.TransitiveGround.codedFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.nameDomain`, `OAI.PartitionPilot.Forcing.TransitiveGround.niceSupportNameCodes`, `OAI.PartitionPilot.SetRealization.Presentation.pairEmpty` and `OAI.PartitionPilot.Forcing.Name.NameDomain` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.supportedCertificateFamilyFormula`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decodedAction`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decoded_action_eq`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decoded_order_eq`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decoded_supportBasis_ground`, `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.niceAssignmentClassGraphs`, `OAI.PartitionPilot.Forcing.TransitiveGround.niceRefinementIndices`, `OAI.PartitionPilot.Forcing.TransitiveGround.visibleSupportProfile` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder_code` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel`, `OAI.PartitionPilot.Forcing.GroundMainPrefix` and `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decoded_directed` (definitions bundle `OAIQ253P006` of this split); `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory`, `OAI.PartitionPilot.Forcing.RecursiveRefinementDataHistory.restrict`, `OAI.PartitionPilot.Forcing.TransitiveGround.certificateEnumerationRelation`, `OAI.PartitionPilot.Forcing.TransitiveGround.conditionMapFamily_mem_of_actionGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryOrderTop`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryPartialOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.supportedEqualityCertificateBound` and `OAI.PartitionPilot.Forcing.TransitiveGround.synchronizedEnumerationBound` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.supportedCertificateFamilyRelation` (definitions bundle `OAIQ253P008` of this split); `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.finalGeometry`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryRowNameFamily_valid`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStage`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingTrace_recursiveOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory` and `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixAction`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_preparation_inputs` and `OAI.PartitionPilot.Forcing.TransitiveGround.supportedCertificateFamilyEnv` (definitions bundle `OAIQ253P011` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.setTransitive`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet`, `OAI.PartitionPilot.Forcing.SetFormula.union` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundEmbeddable` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_groundFairPreparationOrbit` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundMainFinalPrefixPreparationBatches.lean (declaration OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_prefixPreparationBatch)

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
variable {R : Type u} [PartialOrder R] (c : Presentation R)

theorem exists_prefixPreparationBatch
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (rowClosed : InternallyCountablyClosed M c) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) R) (T T2 rowTop : ZFSet.{u})
      (carrier : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
      (rowAction : a.actionGraph c t ∈ M.sets)
      (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (topMem : rowTop ∈ c.carrier)
      (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder),
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
    ∀ (stages history alpha : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
      (member : alpha ∈ stages),
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
  let inputs := M.semanticStructuralPrefix_preparation_inputs c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
      infinite choice rowClosed
  let lowerGround := inputs.1
  let maps := inputs.2.2.1
  let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
    ∀ (row A : ZFSet.{u}) (_condition : ZFSet.pair row A ∈
      M.refinementHistoryForcing c.carrier T stages packed),
  let selected := assignmentOnIndices indices T A
  let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
  let bound := M.groundRelations T lower.carrier
  let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
    ∀ (H : ConditionFilter (SetMembers Q))
      (_genericCoded : H.GenericFor (M.codedFamily lower))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain lower)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ lowerAct.stabilizer lower x.val →
        d.principalFix w ≤ lowerAct.stabilizer lower y.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain lower).names,
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ lowerAct.stabilizer lower τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (p : SetMembers Q) (_hp : H.mem p),
      ∃ (validJ : ∀ z ∈ J, IsName lower z) (hJ : J ∈ M.sets),
        M.groundEmbeddable J ZFSet.omega ∧
        (∀ z : Name lower, z.val ∈ J →
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) z ∧
          Name.eval {q | H.mem q} z ⊆ Name.eval {q | H.mem q} (Name.familySet ⊤ T valid)) ∧
      ∃ (k : ZFSet.{u}) (hk : k ∈ M.sets),
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
          (M.niceSupportNameCodes lowerAct lower T d.principalFix)) k ∧
        k ⊆ M.supportedCertificateFamilyRelation lowerAct lower b T d.principalFix
          geometry.order J validJ H ∧
        ∃ q, H.mem q ∧ q ≤ p ∧
          Forces (M.nameDomain lower) supportedCertificateFamilyFormula
            (M.supportedCertificateFamilyEnv lowerAct lower t b T d.principalFix pairing unions powers
              separation collection lowerGround geometry.actors_ground geometry.carrier_ground
              (geometry.decoded_supportBasis_ground pairing unions powers separation)
              maps hT valid (M.omega_mem separation infinite) geometry.order J k
              geometry.order_ground hJ hk validJ) q ∧
          ∃ enumerations ∈ M.sets,
            ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier
              (M.niceSupportNameCodes lowerAct lower T d.principalFix)) enumerations ∧
            enumerations ⊆ M.certificateEnumerationRelation J b.carrier
              (M.niceSupportNameCodes lowerAct lower T d.principalFix) k ∧
            (∀ j F B f e names,
              ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              ZFSet.pair j (ZFSet.pair e names) ∈ enumerations →
              SynchronizedEnumerationCode ZFSet.omega
                (M.niceSupportNameCodes lowerAct lower T d.principalFix) B f e names) ∧
            ∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
              ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              F = M.visibleSupportProfile lowerAct lower b d T H (Name.eval {p | H.mem p} z.val) ∧
              MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
              B.Nonempty ∧ M.DecidesVisibilityProfile lowerAct lower b d.principalFix T F z.val q ∧
              (∀ v ∈ B, ∀ tau : Name lower, tau.val ∈ M.niceSupportNameCodes lowerAct lower T d.principalFix →
                ZFSet.pair v tau.val ∈ f → Name.ForcesEq q z.val tau) ∧
              ∃ e ∈ M.sets, ∃ names ∈ M.sets,
                ZFSet.IsFunc ZFSet.omega B e ∧
                ZFSet.IsFunc ZFSet.omega (M.niceSupportNameCodes lowerAct lower T d.principalFix) names ∧
                (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
                (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                  ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
                (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                  ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names) := by
  sorry

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end
