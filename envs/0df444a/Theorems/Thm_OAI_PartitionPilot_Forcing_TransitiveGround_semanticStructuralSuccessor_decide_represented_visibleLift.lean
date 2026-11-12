-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralSuccessor_decide_represented_visibleLift
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_decide_represented_visibleLift
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:33:43.887339+00:00
-- url     : https://prove2.me/theorems/1fc8ee18-291c-4239-bbf2-b76f0d4ee7c2
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_decide_represented_visibleLift: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_decide_represented_visibleLift` of [lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticRepresentedDomainLiftDecisions.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticRepresentedDomainLiftDecisions.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open SetRealization SetFormula`):
--
--   ```lean
--   theorem semanticStructuralSuccessor_decide_represented_visibleLift
--       (infinite : Realize M.sets infinity Fin.elim0)
--       (choice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable)
--       {row A : ZFSet.{u}} (condition : ZFSet.pair row A ∈ upper) :
--       letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
--       letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
--         ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
--       let lower := SetMembers.presentation Q
--       let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
--         cutOrdinal carrier T valid1
--       let system := M.semanticStructuralPrefix_refinementSystem c a t b d base directed T T2 rowTop
--         pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
--         nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
--         topMem topRows hs hh ordinal trace member
--       let lowerOrder : lower.conditionOrder ∈ M.sets := by
--         rw [M.refinementHistoryDecodedOrder_eq]
--         exact orderGround
--       let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
--       let vis := M.stageOneVisibilityName lower valid act b d base directed system.first
--
--       ∀ (C E : L) (U Rf Rc u : (M.nameDomain lower).names),
--         let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
--         idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid → u.val.val ∈ T →
--         ∀ pCut r : SetMembers Q,
--         lower.encode pCut = ZFSet.pair row (assignmentCut levels alpha A) → r ≤ pCut →
--         Name.ForcesMem r u.val U.val →
--         (∀ v z : (M.nameDomain lower).names, v.val.val ∈ T → z.val.val ∈ T →
--           stageOneAssignment idx v.val.val z.val.val ∈ A →
--           ∀ q, q ≤ r → ¬ Name.ForcesEq q (cls Rc u).val (cls Rc v).val) →
--         let quotient : (M.nameDomain lower).names := ⟨Name.refinementQuotient T valid U.val Rf.val,
--           M.refinementQuotient_mem lower pairing unions powers separation collection lowerGround lowerOrder
--             hT valid U.val Rf.val U.property Rf.property⟩
--         let map := M.stageOneMapName lower pairing unions powers separation collection
--           lowerGround lowerOrder hT valid U Rf Rc
--         ∃ q, q ≤ r ∧ Name.ForcesMem q u.val U.val ∧
--           (∀ v z : (M.nameDomain lower).names, v.val.val ∈ T → z.val.val ∈ T →
--             stageOneAssignment idx v.val.val z.val.val ∈ A →
--             ∀ k, k ≤ q → ¬ Name.ForcesEq k (cls Rc u).val (cls Rc v).val) ∧
--           ((Forces (M.nameDomain lower) refinementVisibleLiftFormula
--               ![quotient, vis C, cls Rc u, map] q ∧
--             ∃ w : (M.nameDomain lower).names, w.val.val ∈ T ∧
--               Name.ForcesMem q u.val U.val ∧ Name.ForcesMem q w.val U.val ∧
--               ∃ lowerRow lowerA : ZFSet.{u}, lower.encode q = ZFSet.pair lowerRow lowerA ∧
--                 let spliced := assignmentSplice levels alpha lowerA A
--                 let inserted := insert (stageOneAssignment idx u.val.val w.val.val) spliced
--                 ZFSet.pair lowerRow inserted ∈ upper ∧
--                 ZFSet.pair (ZFSet.pair lowerRow inserted) (ZFSet.pair row A) ∈
--                   M.refinementHistoryOrder c.carrier c.conditionOrder T (insert alpha alpha) next ∧
--                 A ⊆ inserted ∧ stageOneAssignment idx u.val.val w.val.val ∈ inserted ∧
--                 ZFSet.pair lowerRow (assignmentCut levels alpha inserted) = lower.encode q ∧
--                 Name.ForcesEq q (cls Rc u).val (cls Rc u).val ∧
--                 ZFSet.pair lowerRow inserted ∈ M.representedDomainConditions lower upper levels alpha T valid
--                   idx U Rc u) ∨
--           (Forces (M.nameDomain lower) (.neg refinementVisibleLiftFormula)
--               ![quotient, vis C, cls Rc u, map] q ∧
--             Name.ForcesMem q (cls Rf u).val quotient.val ∧
--             Forces (M.nameDomain lower) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
--               ![cls Rf u, cls Rc u, map] q ∧
--             ∀ k, k ≤ q → ¬ Name.ForcesMem k (cls Rf u).val (vis C).val))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.Forcing.stageOneAssignment`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph` and `OAI.PartitionPilot.SetRealization.SetMembers.presentation` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.assignmentCut`, `OAI.PartitionPilot.Forcing.assignmentSplice`, `OAI.PartitionPilot.Forcing.graphRestriction`, `OAI.PartitionPilot.Forcing.ordinalSetProperty_member` and `OAI.PartitionPilot.Forcing.SetFormula.refinementVisibleLiftFormula` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.refinementIndexCode`, `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace`, `OAI.PartitionPilot.Forcing.Name.ForcesEq`, `OAI.PartitionPilot.Forcing.Name.ForcesMem`, `OAI.PartitionPilot.Forcing.Name.refinementQuotient`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.PosetAction.conditionMapFamily`, `OAI.PartitionPilot.Forcing.SetFormula.Forces`, `OAI.PartitionPilot.Forcing.TransitiveGround.nameDomain`, `OAI.PartitionPilot.SetRealization.Presentation.pairEmpty` and `OAI.PartitionPilot.Forcing.Name.NameDomain` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.graphRestriction_mem` (definitions bundle `OAIQ253P004` of this split); `OAI.PartitionPilot.Forcing.refinementDataHistoryLevels`, `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.niceRefinementIndices`, `OAI.PartitionPilot.Forcing.TransitiveGround.representedDomainConditions`, `OAI.PartitionPilot.Forcing.TransitiveGround.stageOneVisibilityName` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder_code` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.RefinementStageSystem`, `OAI.PartitionPilot.Forcing.RecursiveRefinementDataHistory.restrict`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryOrderTop`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryPartialOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementQuotient_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.stageOneClassName` and `OAI.PartitionPilot.Forcing.TransitiveGround.stageOneMapName` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryDecodedOrder_eq`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryOrder_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryRowNameFamily_valid`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStage`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingTrace_recursiveOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory_mem` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixAction` and `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_refinementSystem` (definitions bundle `OAIQ253P011` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.setTransitive`, `OAI.PartitionPilot.Forcing.BoundedFormula.pairMembershipFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.toFormula`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet` and `OAI.PartitionPilot.Forcing.SetFormula.union` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_represented_domain_dense` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticRepresentedDomainLiftDecisions.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_decide_represented_visibleLift)

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

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

local notation "next" => graphRestriction (insert alpha alpha) packed
local notation "upper" => M.refinementHistoryForcing c.carrier T (insert alpha alpha) next
local notation "levels" => refinementDataHistoryLevels (insert alpha alpha) next T
local notation "packedGround" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
local notation "lowerGround" => M.refinementHistoryForcing_mem pairing unions powers separation
  carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha packedGround) omega
local notation "orderGround" => M.refinementHistoryOrder_mem pairing unions powers separation
  carrier rowOrderGround hT hAlpha (M.graphRestriction_mem unions separation hAlpha packedGround) omega

theorem semanticStructuralSuccessor_decide_represented_visibleLift
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable)
    {row A : ZFSet.{u}} (condition : ZFSet.pair row A ∈ upper) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let system := M.semanticStructuralPrefix_refinementSystem c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member
    let lowerOrder : lower.conditionOrder ∈ M.sets := by
      rw [M.refinementHistoryDecodedOrder_eq]
      exact orderGround
    let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
    let vis := M.stageOneVisibilityName lower valid act b d base directed system.first

    ∀ (C E : L) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid → u.val.val ∈ T →
      ∀ pCut r : SetMembers Q,
      lower.encode pCut = ZFSet.pair row (assignmentCut levels alpha A) → r ≤ pCut →
      Name.ForcesMem r u.val U.val →
      (∀ v z : (M.nameDomain lower).names, v.val.val ∈ T → z.val.val ∈ T →
        stageOneAssignment idx v.val.val z.val.val ∈ A →
        ∀ q, q ≤ r → ¬ Name.ForcesEq q (cls Rc u).val (cls Rc v).val) →
      let quotient : (M.nameDomain lower).names := ⟨Name.refinementQuotient T valid U.val Rf.val,
        M.refinementQuotient_mem lower pairing unions powers separation collection lowerGround lowerOrder
          hT valid U.val Rf.val U.property Rf.property⟩
      let map := M.stageOneMapName lower pairing unions powers separation collection
        lowerGround lowerOrder hT valid U Rf Rc
      ∃ q, q ≤ r ∧ Name.ForcesMem q u.val U.val ∧
        (∀ v z : (M.nameDomain lower).names, v.val.val ∈ T → z.val.val ∈ T →
          stageOneAssignment idx v.val.val z.val.val ∈ A →
          ∀ k, k ≤ q → ¬ Name.ForcesEq k (cls Rc u).val (cls Rc v).val) ∧
        ((Forces (M.nameDomain lower) refinementVisibleLiftFormula
            ![quotient, vis C, cls Rc u, map] q ∧
          ∃ w : (M.nameDomain lower).names, w.val.val ∈ T ∧
            Name.ForcesMem q u.val U.val ∧ Name.ForcesMem q w.val U.val ∧
            ∃ lowerRow lowerA : ZFSet.{u}, lower.encode q = ZFSet.pair lowerRow lowerA ∧
              let spliced := assignmentSplice levels alpha lowerA A
              let inserted := insert (stageOneAssignment idx u.val.val w.val.val) spliced
              ZFSet.pair lowerRow inserted ∈ upper ∧
              ZFSet.pair (ZFSet.pair lowerRow inserted) (ZFSet.pair row A) ∈
                M.refinementHistoryOrder c.carrier c.conditionOrder T (insert alpha alpha) next ∧
              A ⊆ inserted ∧ stageOneAssignment idx u.val.val w.val.val ∈ inserted ∧
              ZFSet.pair lowerRow (assignmentCut levels alpha inserted) = lower.encode q ∧
              Name.ForcesEq q (cls Rc u).val (cls Rc u).val ∧
              ZFSet.pair lowerRow inserted ∈ M.representedDomainConditions lower upper levels alpha T valid
                idx U Rc u) ∨
        (Forces (M.nameDomain lower) (.neg refinementVisibleLiftFormula)
            ![quotient, vis C, cls Rc u, map] q ∧
          Name.ForcesMem q (cls Rf u).val quotient.val ∧
          Forces (M.nameDomain lower) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
            ![cls Rf u, cls Rc u, map] q ∧
          ∀ k, k ≤ q → ¬ Name.ForcesMem k (cls Rf u).val (vis C).val)) := by
  sorry

end PartitionPilot.Forcing.TransitiveGround

end OAI
end
