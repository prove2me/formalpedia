-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_countableRow_semanticStructuralTrace_jointZF_sequenceReflection
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.countableRow_semanticStructuralTrace_jointZF_sequenceReflection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:25:33.024244+00:00
-- url     : https://prove2.me/theorems/8fa11b8d-218b-41d5-bdcb-a48eb6ba0e55
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.countableRow_semanticStructuralTrace_jointZF_sequenceReflection: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.countableRow_semanticStructuralTrace_jointZF_sequenceReflection` of [lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundCountableRowSequenceReflection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundCountableRowSequenceReflection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open SetRealization SetFormula`):
--
--   ```lean
--   theorem countableRow_semanticStructuralTrace_jointZF_sequenceReflection
--       (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
--       (unions : Realize M.sets SetFormula.union Fin.elim0)
--       (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
--       (collection : CollectionSchema M.sets)
--       (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       (X : ZFSet.{u}) (hX : X ∈ M.sets) (small : M.sets.Countable) :
--       letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
--       let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
--       ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
--         (T T2 rowTop : ZFSet.{u})
--       (rowAction : a.actionGraph c t ∈ M.sets)
--       (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
--       (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
--       (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
--       (supports : supportBasisCode b t d.principalFix ∈ M.sets)
--       (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
--       (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
--       (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
--       (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
--       (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
--       (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
--     HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
--       (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
--     HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
--       (topMem : rowTop ∈ c.carrier)
--       (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
--       (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
--       (ordinal : ordinalSetProperty stages)
--       (trace : OrdinalRecursionTrace (fun level prior stage => stage =
--         M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
--           t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
--           (supportBasisCode b t d.principalFix) T T2 level prior) stages history),
--       let two := M.natSetCode_mem separation infinite 2
--       let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX two
--       let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX two
--       let omega := M.omega_mem separation infinite
--       let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
--         (supportBasisCode b t d.principalFix) T T2 stages history
--       let Q := M.refinementHistoryForcing c.carrier T stages packed
--       let Cuts := {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ⊆ stages}
--       let lower := (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier T (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
--       let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
--         t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
--       let witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
--       let mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
--         pairing unions powers separation collection group nodes supports hh hT witnesses
--       let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
--         ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
--         (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
--           (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
--       letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
--       let act := M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
--       letI : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
--         M.refinementHistoryPartialOrder c.conditionOrder_code T j.val (graphRestriction j.val packed)
--       let restrictions : ∀ j : Cuts, SetMembers Q →o lower j := fun j =>
--         (run).restriction ordinal j.property.2.1 j.property.2.2 c.conditionOrder_code
--       let inclusions : ∀ j : Cuts, lower j ↪o SetMembers Q := fun j =>
--         (run).inclusion ordinal j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
--           hs hPacked hT j.property.1 carrier rowTop topMem topRows mono c.conditionOrder_code
--       let projections : ∀ j, CompleteProjection (restrictions j) (inclusions j) := fun j =>
--         M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace j.val j.property.1
--           j.property.2.1 j.property.2.2 infinite choice
--       let s := SetMembers.presentation Q
--       let F := d.principalSupportFamily base directed
--       ∀ p : SetMembers Q, ∃ H : ConditionFilter (SetMembers Q),
--         H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
--         H.GenericFor (formulaFamily (M.nameDomain s)) ∧
--         H.GenericFor (formulaFamily ((act).symmetricDomain s (M.nameDomain s) F)) ∧
--         (∀ j : Cuts,
--           ((projections j).projectedFilter H).GenericFor
--             (M.codedFamily (SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))) ∧
--           ((projections j).projectedFilter H).GenericFor
--             (formulaFamily (M.nameDomain (SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))))) ∧
--         M.sets ⊆ ((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q} ∧
--         ZFRealization (((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q}) ∧
--         (∀ U ∈ M.sets,
--           GroundSequenceReflection M (M.ordinaryExtension s H) U ∧
--           GroundSequenceReflection M (M.symmetricExtension s (act) F H) U)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.Forcing.natSetCode`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Compression.RecursiveMaps.NormalSubgroupFamily`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.natSetCode_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.omega_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallFunctionOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallPartialFunctions` and `OAI.PartitionPilot.SetRealization.SetMembers.presentation` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.CompleteProjection`, `OAI.PartitionPilot.Forcing.ConditionFilter`, `OAI.PartitionPilot.Forcing.graphRestriction`, `OAI.PartitionPilot.Forcing.CompleteProjection.projectedFilter` and `OAI.PartitionPilot.Forcing.ConditionFilter.GenericFor` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.refinementFormulaDataCode`, `OAI.PartitionPilot.Forcing.stageOneRawTests`, `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.GroundSequenceReflection`, `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace`, `OAI.PartitionPilot.Forcing.forcingStageCode`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.PosetAction.conditionMapFamily`, `OAI.PartitionPilot.Forcing.PosetAction.symmetricDomain`, `OAI.PartitionPilot.Forcing.SetFormula.formulaFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.codedFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.nameDomain`, `OAI.PartitionPilot.Forcing.TransitiveGround.ordinaryExtension`, `OAI.PartitionPilot.Forcing.TransitiveGround.symmetricExtension`, `OAI.PartitionPilot.SetRealization.Presentation.pairEmpty` and `OAI.PartitionPilot.Forcing.Name.NameDomain.values` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.countableFunctionOrder_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.countablePartialFunctions_mem` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder_code` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.RawRefinementStageWitness`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory.inclusion`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory.restriction`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing` and `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryPartialOrder` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStage`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingTrace_recursiveOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingTrace_witnesses`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory_mem` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAction`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_completeProjection` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralHistory_rawTests_mono` (definitions bundle `OAIQ253P011` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.ZFRealization`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet` and `OAI.PartitionPilot.Forcing.SetFormula.union` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_rowSemanticQuotientInjectionModel` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundCountableRowSequenceReflection.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.countableRow_semanticStructuralTrace_jointZF_sequenceReflection)

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

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G L : Type u} [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem countableRow_semanticStructuralTrace_jointZF_sequenceReflection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X : ZFSet.{u}) (hX : X ∈ M.sets) (small : M.sets.Countable) :
    letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
    let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
    ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
      (T T2 rowTop : ZFSet.{u})
    (rowAction : a.actionGraph c t ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
    (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
    (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
    (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
    (topMem : rowTop ∈ c.carrier)
    (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history),
    let two := M.natSetCode_mem separation infinite 2
    let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX two
    let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX two
    let omega := M.omega_mem separation infinite
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let Cuts := {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ⊆ stages}
    let lower := (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier T (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
    let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
    let witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
    let mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
      pairing unions powers separation collection group nodes supports hh hT witnesses
    let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
      ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
      (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
        (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    let act := M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
    letI : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
      M.refinementHistoryPartialOrder c.conditionOrder_code T j.val (graphRestriction j.val packed)
    let restrictions : ∀ j : Cuts, SetMembers Q →o lower j := fun j =>
      (run).restriction ordinal j.property.2.1 j.property.2.2 c.conditionOrder_code
    let inclusions : ∀ j : Cuts, lower j ↪o SetMembers Q := fun j =>
      (run).inclusion ordinal j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
        hs hPacked hT j.property.1 carrier rowTop topMem topRows mono c.conditionOrder_code
    let projections : ∀ j, CompleteProjection (restrictions j) (inclusions j) := fun j =>
      M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace j.val j.property.1
        j.property.2.1 j.property.2.2 infinite choice
    let s := SetMembers.presentation Q
    let F := d.principalSupportFamily base directed
    ∀ p : SetMembers Q, ∃ H : ConditionFilter (SetMembers Q),
      H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily ((act).symmetricDomain s (M.nameDomain s) F)) ∧
      (∀ j : Cuts,
        ((projections j).projectedFilter H).GenericFor
          (M.codedFamily (SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))) ∧
        ((projections j).projectedFilter H).GenericFor
          (formulaFamily (M.nameDomain (SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))))) ∧
      M.sets ⊆ ((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q} ∧
      ZFRealization (((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q}) ∧
      (∀ U ∈ M.sets,
        GroundSequenceReflection M (M.ordinaryExtension s H) U ∧
        GroundSequenceReflection M (M.symmetricExtension s (act) F H) U) := by
  sorry

end PartitionPilot.Forcing.TransitiveGround

end OAI
end
