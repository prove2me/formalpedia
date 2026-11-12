-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralFairPreparation_supported_lower_bound
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralFairPreparation_supported_lower_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:10:12.311711+00:00
-- url     : https://prove2.me/theorems/ba7f33c7-775b-42c2-a137-d270bd1bbe38
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralFairPreparation_supported_lower_bound: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralFairPreparation_supported_lower_bound` of [lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticFairPreparationSupportedLimits.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticFairPreparationSupportedLimits.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open SetRealization SetFormula`):
--
--   ```lean
--   theorem semanticStructuralFairPreparation_supported_lower_bound
--       {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
--       (ordinal : ordinalSetProperty stages)
--       (trace : OrdinalRecursionTrace (fun level prior stage => stage =
--         M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
--           t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
--           (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
--       (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       (rowClosed : InternallyCountablyClosed M c) :
--       let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
--         (supportBasisCode b t d.principalFix) T T2 stages history
--       letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
--       let Q := M.refinementHistoryForcing c.carrier T stages packed
--       let B := M.groundSmallSubsets (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
--       let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
--       let data := flatCarrierData c Q B shape
--       ∀ (p : SetMembers Q) (E0 enumSelector prepSelector orbit e : ZFSet.{u}),
--         E0 ∈ M.sets → orbit ∈ M.sets →
--         ZFSet.IsFunc Q E0 enumSelector →
--         enumSelector ⊆ M.birthLevelEnumerationRelation Q stages (refinementDataHistoryLevels stages packed T) →
--         prepSelector ⊆ M.varyingPreparationRelation stages packed Q
--           (M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed) b.carrier T →
--         ZFSet.pair (SetMembers.raw p) e ∈ enumSelector →
--         ZFSet.IsFunc ZFSet.omega
--           (M.fairPreparationStates Q stages (M.preparationWitnessBound b.carrier T Q) E0 enumSelector) orbit →
--         (∀ state, ZFSet.pair ∅ state ∈ orbit ↔
--           state = ZFSet.pair ∅ (ZFSet.pair (SetMembers.raw p) (ZFSet.pair {ZFSet.pair ∅ e} ∅))) →
--         (∀ n ∈ ZFSet.omega, ∀ state next,
--           ZFSet.pair n state ∈ orbit → ZFSet.pair (insert n n) next ∈ orbit →
--           FairPreparationStepCode ZFSet.omega E0 stages (M.preparationWitnessBound b.carrier T Q)
--             enumSelector prepSelector
--             (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv) state next) →
--         ∃ seq : Nat → SetMembers Q, seq 0 = p ∧ groundSequenceGraph seq ∈ M.sets ∧ Antitone seq ∧
--         ∃ clocks births events : Nat → ZFSet.{u},
--           clocks 0 = ∅ ∧ births 0 = {ZFSet.pair ∅ e} ∧ events 0 = ∅ ∧
--           (∀ k, ZFSet.pair (natSetCode k)
--             (ZFSet.pair (clocks k) (ZFSet.pair (SetMembers.raw (seq k))
--               (ZFSet.pair (births k) (events k)))) ∈ orbit) ∧
--           familyCodeGraph natSetCode events ∈ M.sets ∧
--           ZFSet.IsFunc ZFSet.omega
--             (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
--             (familyCodeGraph natSetCode events) ∧
--           M.preparationUsedSupportUnion b.carrier
--             (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
--             (familyCodeGraph natSetCode events) ∈ M.sets ∧
--           M.preparationUsedSupportUnion b.carrier
--             (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
--             (familyCodeGraph natSetCode events) ⊆ b.carrier ∧
--           M.groundEmbeddable (M.preparationUsedSupportUnion b.carrier
--             (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
--             (familyCodeGraph natSetCode events)) ZFSet.omega ∧
--           (∀ k, FairPreparationStepCode ZFSet.omega E0 stages (M.preparationWitnessBound b.carrier T Q)
--             enumSelector prepSelector
--             (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv)
--             (ZFSet.pair (clocks k) (ZFSet.pair (SetMembers.raw (seq k)) (ZFSet.pair (births k) (events k))))
--             (ZFSet.pair (clocks (k + 1))
--               (ZFSet.pair (SetMembers.raw (seq (k + 1))) (ZFSet.pair (births (k + 1)) (events (k + 1)))))) ∧
--         ∃ limit : SetMembers Q, (∀ n, limit ≤ seq n) ∧
--           SetMembers.raw (data limit) = stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∧
--           stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∈ M.sets ∧
--           (∀ z, z ∈ SetMembers.raw (data limit) ↔ ∃ n, z ∈ SetMembers.raw (data (seq n))) ∧
--           ∀ x ∈ SetMembers.raw (data limit),
--             ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
--               Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
--               x ∈ SetMembers.raw (data (seq i)) ∧
--               ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
--               ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages packed T ∧
--               (∀ k, Nat.pair i j ≤ k →
--                 x ∈ assignmentOnIndices (fields 0) T (SetMembers.raw (data (seq k)))) ∧
--               ∃ y ∈ M.preparationWitnessBound b.carrier T Q, ∃ payload,
--                 y = ZFSet.pair (SetMembers.raw (seq (Nat.pair i j + 1))) payload ∧
--                 ZFSet.pair (ZFSet.pair alpha (SetMembers.raw (seq (Nat.pair i j)))) y ∈ prepSelector ∧
--                 events (Nat.pair i j + 1) = ZFSet.pair alpha y
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.Forcing.natPresentation`, `OAI.PartitionPilot.Forcing.natSetCode`, `OAI.PartitionPilot.Forcing.stageOneAssignments`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph`, `OAI.PartitionPilot.SetRealization.Presentation.graph`, `OAI.PartitionPilot.SetRealization.Presentation.product` and `OAI.PartitionPilot.SetRealization.SetMembers.raw` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.FairPreparationStepCode`, `OAI.PartitionPilot.Forcing.familyCodeGraph`, `OAI.PartitionPilot.Forcing.omegaGridEquiv` and `OAI.PartitionPilot.Forcing.stageOneAssignmentUnion` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.refinementDataHistoryIndices`, `OAI.PartitionPilot.Forcing.refinementFormulaDataCode`, `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.InternallyCountablyClosed`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace`, `OAI.PartitionPilot.Forcing.assignmentOnIndices`, `OAI.PartitionPilot.Forcing.groundSequenceGraph`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.PosetAction.conditionMapFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.groundSmallSubsets` and `OAI.PartitionPilot.SetRealization.Presentation.pairEmpty` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.flatCarrierData`, `OAI.PartitionPilot.Forcing.refinementDataHistoryLevels`, `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder_code` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.birthLevelEnumerationRelation`, `OAI.PartitionPilot.Forcing.TransitiveGround.preparationWitnessBound`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing_shape`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryPartialOrder` and `OAI.PartitionPilot.Forcing.TransitiveGround.varyingPreparationRelation` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.fairPreparationStates` and `OAI.PartitionPilot.Forcing.TransitiveGround.preparationUsedSupportUnion` (definitions bundle `OAIQ253P008` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStage` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet`, `OAI.PartitionPilot.Forcing.SetFormula.union` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundEmbeddable` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_support_prepared_strengthening` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticFairPreparationSupportedLimits.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralFairPreparation_supported_lower_bound)

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

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

theorem semanticStructuralFairPreparation_supported_lower_bound
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (rowClosed : InternallyCountablyClosed M c) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let B := M.groundSmallSubsets (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
    let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
    let data := flatCarrierData c Q B shape
    ∀ (p : SetMembers Q) (E0 enumSelector prepSelector orbit e : ZFSet.{u}),
      E0 ∈ M.sets → orbit ∈ M.sets →
      ZFSet.IsFunc Q E0 enumSelector →
      enumSelector ⊆ M.birthLevelEnumerationRelation Q stages (refinementDataHistoryLevels stages packed T) →
      prepSelector ⊆ M.varyingPreparationRelation stages packed Q
        (M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed) b.carrier T →
      ZFSet.pair (SetMembers.raw p) e ∈ enumSelector →
      ZFSet.IsFunc ZFSet.omega
        (M.fairPreparationStates Q stages (M.preparationWitnessBound b.carrier T Q) E0 enumSelector) orbit →
      (∀ state, ZFSet.pair ∅ state ∈ orbit ↔
        state = ZFSet.pair ∅ (ZFSet.pair (SetMembers.raw p) (ZFSet.pair {ZFSet.pair ∅ e} ∅))) →
      (∀ n ∈ ZFSet.omega, ∀ state next,
        ZFSet.pair n state ∈ orbit → ZFSet.pair (insert n n) next ∈ orbit →
        FairPreparationStepCode ZFSet.omega E0 stages (M.preparationWitnessBound b.carrier T Q)
          enumSelector prepSelector
          (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv) state next) →
      ∃ seq : Nat → SetMembers Q, seq 0 = p ∧ groundSequenceGraph seq ∈ M.sets ∧ Antitone seq ∧
      ∃ clocks births events : Nat → ZFSet.{u},
        clocks 0 = ∅ ∧ births 0 = {ZFSet.pair ∅ e} ∧ events 0 = ∅ ∧
        (∀ k, ZFSet.pair (natSetCode k)
          (ZFSet.pair (clocks k) (ZFSet.pair (SetMembers.raw (seq k))
            (ZFSet.pair (births k) (events k)))) ∈ orbit) ∧
        familyCodeGraph natSetCode events ∈ M.sets ∧
        ZFSet.IsFunc ZFSet.omega
          (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
          (familyCodeGraph natSetCode events) ∧
        M.preparationUsedSupportUnion b.carrier
          (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
          (familyCodeGraph natSetCode events) ∈ M.sets ∧
        M.preparationUsedSupportUnion b.carrier
          (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
          (familyCodeGraph natSetCode events) ⊆ b.carrier ∧
        M.groundEmbeddable (M.preparationUsedSupportUnion b.carrier
          (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
          (familyCodeGraph natSetCode events)) ZFSet.omega ∧
        (∀ k, FairPreparationStepCode ZFSet.omega E0 stages (M.preparationWitnessBound b.carrier T Q)
          enumSelector prepSelector
          (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv)
          (ZFSet.pair (clocks k) (ZFSet.pair (SetMembers.raw (seq k)) (ZFSet.pair (births k) (events k))))
          (ZFSet.pair (clocks (k + 1))
            (ZFSet.pair (SetMembers.raw (seq (k + 1))) (ZFSet.pair (births (k + 1)) (events (k + 1)))))) ∧
      ∃ limit : SetMembers Q, (∀ n, limit ≤ seq n) ∧
        SetMembers.raw (data limit) = stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∧
        stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∈ M.sets ∧
        (∀ z, z ∈ SetMembers.raw (data limit) ↔ ∃ n, z ∈ SetMembers.raw (data (seq n))) ∧
        ∀ x ∈ SetMembers.raw (data limit),
          ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
            Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
            x ∈ SetMembers.raw (data (seq i)) ∧
            ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
            ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages packed T ∧
            (∀ k, Nat.pair i j ≤ k →
              x ∈ assignmentOnIndices (fields 0) T (SetMembers.raw (data (seq k)))) ∧
            ∃ y ∈ M.preparationWitnessBound b.carrier T Q, ∃ payload,
              y = ZFSet.pair (SetMembers.raw (seq (Nat.pair i j + 1))) payload ∧
              ZFSet.pair (ZFSet.pair alpha (SetMembers.raw (seq (Nat.pair i j)))) y ∈ prepSelector ∧
              events (Nat.pair i j + 1) = ZFSet.pair alpha y := by
  sorry

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end
