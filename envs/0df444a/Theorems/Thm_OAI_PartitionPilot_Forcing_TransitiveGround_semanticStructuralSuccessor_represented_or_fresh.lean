-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralSuccessor_represented_or_fresh
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_or_fresh
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:36:15.901039+00:00
-- url     : https://prove2.me/theorems/f6644d1b-ad27-47cb-a8b9-fb64775c16e5
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_or_fresh: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_or_fresh` of [lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticRepresentedDomainEasyCases.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticRepresentedDomainEasyCases.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open SetRealization SetFormula`):
--
--   ```lean
--   theorem semanticStructuralSuccessor_represented_or_fresh
--       (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
--       (unions : Realize M.sets SetFormula.union Fin.elim0)
--       (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
--       (collection : CollectionSchema M.sets)
--       (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       (X : ZFSet.{u}) (hX : X ∈ M.sets) :
--       letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
--       let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
--       ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
--         (T T2 rowTop : ZFSet.{u}),
--         ∀ (rowAction : a.actionGraph c t ∈ M.sets)
--           (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
--           (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
--           (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
--           (supports : supportBasisCode b t d.principalFix ∈ M.sets)
--           (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
--           (valid1 : ∀ z ∈ T, IsName c.pairEmpty z) (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
--           (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
--           (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
--           (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
--             HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
--           (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
--             HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
--           (topMem : rowTop ∈ c.carrier)
--           (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
--           (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
--           (ordinal : ordinalSetProperty stages)
--           (trace : OrdinalRecursionTrace (fun level prior stage => stage =
--             M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
--               t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
--               (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
--           (alpha : ZFSet.{u}) (member : alpha ∈ stages),
--         let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
--           (supportBasisCode b t d.principalFix) T T2 stages history
--         let lowerPacked := graphRestriction alpha packed
--         let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
--         let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
--           (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
--           (supportBasisCode b t d.principalFix) T T2 ordinal trace
--         let cutOrdinal := ordinalSetProperty_member ordinal member
--         let subset := (And.left ordinal) alpha member
--         let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX
--           (M.natSetCode_mem separation infinite 2)
--         let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX
--           (M.natSetCode_mem separation infinite 2)
--         ∀ {row A : ZFSet.{u}},
--         ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed →
--         letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
--         letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
--           (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
--         let lower := SetMembers.presentation Q
--         let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
--           cutOrdinal carrier T valid1
--         let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
--           pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
--           nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite)
--           valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace
--           (M.transitive hs member) cutOrdinal subset
--       ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
--         refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
--           M.niceRefinementIndices act lower b d alpha T T2 valid →
--         ∀ u : Name lower, ∀ (hu : u.val ∈ T),
--         ∃ pCut r : SetMembers Q,
--           lower.encode pCut = ZFSet.pair row (assignmentCut
--             (refinementDataHistoryLevels stages packed T) alpha A) ∧ r ≤ pCut ∧
--           ∃ lowerRow lowerA : ZFSet.{u}, lower.encode r = ZFSet.pair lowerRow lowerA ∧
--             let liftedA := assignmentSplice (refinementDataHistoryLevels stages packed T) alpha lowerA A
--             ZFSet.pair lowerRow liftedA ∈ M.refinementHistoryForcing c.carrier T stages packed ∧
--             ZFSet.pair (ZFSet.pair lowerRow liftedA) (ZFSet.pair row A) ∈
--               M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
--             A ⊆ liftedA ∧
--             ZFSet.pair lowerRow (assignmentCut (refinementDataHistoryLevels stages packed T) alpha liftedA) =
--               lower.encode r ∧
--             (ZFSet.pair lowerRow liftedA ∈ M.representedDomainConditions lower
--               (M.refinementHistoryForcing c.carrier T stages packed)
--               (refinementDataHistoryLevels stages packed T) alpha T valid
--               (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
--               U Rc ⟨u, M.transitive hT hu⟩ ∨
--             (Name.ForcesMem r u U.val ∧
--               ∀ v w : Name lower, v.val ∈ T → w.val ∈ T →
--                 stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
--                   U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A →
--                 ∀ q, q ≤ r → ¬ Name.ForcesEq q (Name.refinementClass T valid Rc.val u)
--                   (Name.refinementClass T valid Rc.val v)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.Forcing.natSetCode`, `OAI.PartitionPilot.Forcing.stageOneAssignment`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.natSetCode_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.omega_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallFunctionOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallPartialFunctions` and `OAI.PartitionPilot.SetRealization.SetMembers.presentation` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.assignmentCut`, `OAI.PartitionPilot.Forcing.assignmentSplice`, `OAI.PartitionPilot.Forcing.graphRestriction` and `OAI.PartitionPilot.Forcing.ordinalSetProperty_member` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.refinementIndexCode`, `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace`, `OAI.PartitionPilot.Forcing.Name.ForcesEq`, `OAI.PartitionPilot.Forcing.Name.ForcesMem`, `OAI.PartitionPilot.Forcing.Name.refinementClass`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.PosetAction.conditionMapFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.nameDomain`, `OAI.PartitionPilot.SetRealization.Presentation.pairEmpty` and `OAI.PartitionPilot.Forcing.Name.NameDomain` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.refinementDataHistoryLevels`, `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.countableFunctionOrder_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.countablePartialFunctions_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.niceRefinementIndices`, `OAI.PartitionPilot.Forcing.TransitiveGround.representedDomainConditions` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder_code` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory`, `OAI.PartitionPilot.Forcing.RecursiveRefinementDataHistory.restrict`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryOrderTop` and `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryPartialOrder` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryRowNameFamily_valid`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStage`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingTrace_recursiveOrder` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixAction` (definitions bundle `OAIQ253P011` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.setTransitive`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet` and `OAI.PartitionPilot.Forcing.SetFormula.union` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_represented_domain_dense` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticRepresentedDomainEasyCases.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_or_fresh)

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

theorem semanticStructuralSuccessor_represented_or_fresh
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X : ZFSet.{u}) (hX : X ∈ M.sets) :
    letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
    let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
    ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
      (T T2 rowTop : ZFSet.{u}),
      ∀ (rowAction : a.actionGraph c t ∈ M.sets)
        (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
        (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
        (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
        (supports : supportBasisCode b t d.principalFix ∈ M.sets)
        (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
        (valid1 : ∀ z ∈ T, IsName c.pairEmpty z) (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
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
            (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
        (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
        (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 ordinal trace
      let cutOrdinal := ordinalSetProperty_member ordinal member
      let subset := (And.left ordinal) alpha member
      let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      ∀ {row A : ZFSet.{u}},
      ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed →
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let lower := SetMembers.presentation Q
      let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
        cutOrdinal carrier T valid1
      let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite)
        valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace
        (M.transitive hs member) cutOrdinal subset
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices act lower b d alpha T T2 valid →
      ∀ u : Name lower, ∀ (hu : u.val ∈ T),
      ∃ pCut r : SetMembers Q,
        lower.encode pCut = ZFSet.pair row (assignmentCut
          (refinementDataHistoryLevels stages packed T) alpha A) ∧ r ≤ pCut ∧
        ∃ lowerRow lowerA : ZFSet.{u}, lower.encode r = ZFSet.pair lowerRow lowerA ∧
          let liftedA := assignmentSplice (refinementDataHistoryLevels stages packed T) alpha lowerA A
          ZFSet.pair lowerRow liftedA ∈ M.refinementHistoryForcing c.carrier T stages packed ∧
          ZFSet.pair (ZFSet.pair lowerRow liftedA) (ZFSet.pair row A) ∈
            M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
          A ⊆ liftedA ∧
          ZFSet.pair lowerRow (assignmentCut (refinementDataHistoryLevels stages packed T) alpha liftedA) =
            lower.encode r ∧
          (ZFSet.pair lowerRow liftedA ∈ M.representedDomainConditions lower
            (M.refinementHistoryForcing c.carrier T stages packed)
            (refinementDataHistoryLevels stages packed T) alpha T valid
            (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
            U Rc ⟨u, M.transitive hT hu⟩ ∨
          (Name.ForcesMem r u U.val ∧
            ∀ v w : Name lower, v.val ∈ T → w.val ∈ T →
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A →
              ∀ q, q ≤ r → ¬ Name.ForcesEq q (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v))) := by
  sorry

end PartitionPilot.Forcing.TransitiveGround

end OAI
end
