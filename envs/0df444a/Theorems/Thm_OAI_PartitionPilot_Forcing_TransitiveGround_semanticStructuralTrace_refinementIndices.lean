-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralTrace_refinementIndices
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementIndices
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:36:33.443202+00:00
-- url     : https://prove2.me/theorems/e13bf6e8-59b8-40f4-99f3-2bc783b0ecf5
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementIndices: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementIndices` of [lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticStructuralSymmetricRefinementOutputs.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticStructuralSymmetricRefinementOutputs.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open scoped ZFSet`, `open SetRealization SetFormula Compression.RecursiveMaps`):
--
--   ```lean
--   theorem semanticStructuralTrace_refinementIndices (small : M.sets.Countable)
--       (square : T2 = orderedPairNameFamily (ZFSet.pair rowTop ∅) T T)
--       (growth : ∀ C : L, ∃ E, C < E) :
--       letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
--       letI := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
--         (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
--       let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers
--         (And.left (And.left standard)) carrier T valid1
--       ∀ tau : Fin 3 → (M.nameDomain (SetMembers.presentation Q)).names,
--         (∀ i, HereditarilySymmetric upperAct (SetMembers.presentation Q)
--           (d.principalSupportFamily base directed) (tau i).val) →
--         ∃ beta, ∃ hBeta : beta ∈ K,
--         let hAlpha := M.transitive hK hBeta
--         let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
--         let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
--         letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
--         letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
--           ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
--         let upper := SetMembers.presentation Q
--         let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
--         let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
--           pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
--         let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
--           beta hAlpha cutOrdinal subset infinite choice
--         let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
--         let degrees : Fin 3 → Nat := ![0, 1, 1]
--         let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
--         let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
--         let validT := (termData 0).2 beta cutOrdinal subset
--         ∃ env : Assignment (M.nameDomain lower) 4,
--           (∀ i : Fin 3, (env i.castSucc).val =
--             Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
--           (env 3).val = Name.familySet ⊤ T validT ∧
--         ∃ normalized : Assignment (M.nameDomain lower) 4,
--           (∀ i : Fin 3, (normalized i.castSucc).val =
--             Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
--           normalized 3 = env 3 ∧
--           Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
--           (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
--             (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
--             NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
--             HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
--               (normalized i.castSucc).val) ∧
--           ∃ C E : L, base ≤ C ∧ C < E ∧
--             (∀ i, d.principalFix C ≤ (upperAct).stabilizer upper (tau i).val) ∧
--             refinementIndexCode beta (b.encode C) (b.encode E)
--               (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
--               M.niceRefinementIndices lowerAct lower b d beta T T2 validT ∧
--           ∀ H : ConditionFilter (SetMembers Q),
--             H.GenericFor (formulaFamily (M.nameDomain upper)) →
--             (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
--             (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
--             RefinementValidityCode
--               (Name.eval {p | H.mem p} (Name.familySet ⊤ T validUpper))
--               (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
--               (Name.eval {p | H.mem p} (tau 2).val) →
--             ∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
--               Name.eval {p | H.mem p} (tau i).val
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph`, `OAI.PartitionPilot.SetRealization.SetMembers.presentation` and `OAI.PartitionPilot.Compression.RecursiveMaps.NormalSubgroupFamily` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.CompleteProjection`, `OAI.PartitionPilot.Forcing.ConditionFilter`, `OAI.PartitionPilot.Forcing.RefinementValidityCode`, `OAI.PartitionPilot.Forcing.graphRestriction`, `OAI.PartitionPilot.Forcing.iteratedPairNameFamily`, `OAI.PartitionPilot.Forcing.orderedPairNameFamily`, `OAI.PartitionPilot.Forcing.ordinalSetProperty_member`, `OAI.PartitionPilot.Forcing.CompleteProjection.projectedFilter` and `OAI.PartitionPilot.Forcing.ConditionFilter.GenericFor` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.refinementFormulaDataCode`, `OAI.PartitionPilot.Forcing.refinementIndexCode`, `OAI.PartitionPilot.Forcing.stageOneRawTests`, `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.BoundedFormula.refinementValidityFormula`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.NiceNameCode`, `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace`, `OAI.PartitionPilot.Forcing.forcingStageCode`, `OAI.PartitionPilot.Forcing.Name.crossStageMembershipName`, `OAI.PartitionPilot.Forcing.Name.eval`, `OAI.PartitionPilot.Forcing.Name.familySet`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.PosetAction.conditionMapFamily`, `OAI.PartitionPilot.Forcing.PosetAction.stabilizer`, `OAI.PartitionPilot.Forcing.SetFormula.Assignment`, `OAI.PartitionPilot.Forcing.SetFormula.Forces`, `OAI.PartitionPilot.Forcing.SetFormula.formulaFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.codedFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.nameDomain`, `OAI.PartitionPilot.SetRealization.Presentation.pairEmpty` and `OAI.PartitionPilot.Forcing.Name.NameDomain` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.Name.refinementConditionNames`, `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.niceRefinementIndices` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder_code` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.RawRefinementStageWitness`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory`, `OAI.PartitionPilot.Forcing.RecursiveRefinementDataHistory.restrict`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory.inclusion`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory.inclusionFunction`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory.restriction`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryOrderTop` and `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryPartialOrder` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryRowNameFamily_valid`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStage`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingTrace_recursiveOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingTrace_witnesses`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory_mem` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAction`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixAction`, `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_completeProjection`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralHistory_rawTests_mono` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralTrace_finitePowerTerms` (definitions bundle `OAIQ253P011` of this split); `OAI.PartitionPilot.Forcing.GroundBelow`, `OAI.PartitionPilot.Forcing.GroundCardinalStrongLimit`, `OAI.PartitionPilot.Forcing.GroundCofinalRegular`, `OAI.PartitionPilot.Forcing.GroundStandardInaccessible`, `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.setTransitive`, `OAI.PartitionPilot.Forcing.BoundedFormula.toFormula`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet`, `OAI.PartitionPilot.Forcing.SetFormula.union` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundEmbeddable` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_storedRefinementIndices` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticStructuralSymmetricRefinementOutputs.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementIndices)

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

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem (And.left (And.left standard)) trace

theorem semanticStructuralTrace_refinementIndices (small : M.sets.Countable)
    (square : T2 = orderedPairNameFamily (ZFSet.pair rowTop ∅) T T)
    (growth : ∀ C : L, ∃ E, C < E) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
      (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
    let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers
      (And.left (And.left standard)) carrier T valid1
    ∀ tau : Fin 3 → (M.nameDomain (SetMembers.presentation Q)).names,
      (∀ i, HereditarilySymmetric upperAct (SetMembers.presentation Q)
        (d.principalSupportFamily base directed) (tau i).val) →
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let upper := SetMembers.presentation Q
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      let degrees : Fin 3 → Nat := ![0, 1, 1]
      let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
      let validT := (termData 0).2 beta cutOrdinal subset
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT ∧
      ∃ normalized : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (normalized i.castSucc).val =
          Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
        normalized 3 = env 3 ∧
        Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
        (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
          (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
          NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
            (normalized i.castSucc).val) ∧
        ∃ C E : L, base ≤ C ∧ C < E ∧
          (∀ i, d.principalFix C ≤ (upperAct).stabilizer upper (tau i).val) ∧
          refinementIndexCode beta (b.encode C) (b.encode E)
            (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
            M.niceRefinementIndices lowerAct lower b d beta T T2 validT ∧
        ∀ H : ConditionFilter (SetMembers Q),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
          (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode
            (Name.eval {p | H.mem p} (Name.familySet ⊤ T validUpper))
            (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
            (Name.eval {p | H.mem p} (tau 2).val) →
          ∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (tau i).val := by
  sorry

end PartitionPilot.Forcing.TransitiveGround

end OAI
end
