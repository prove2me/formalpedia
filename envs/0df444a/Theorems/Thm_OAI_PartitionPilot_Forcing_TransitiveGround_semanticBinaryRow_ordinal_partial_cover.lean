-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticBinaryRow_ordinal_partial_cover
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.semanticBinaryRow_ordinal_partial_cover
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:28:12.566126+00:00
-- url     : https://prove2.me/theorems/f098b7dc-25bc-49ab-800f-4bc156b7535f
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.semanticBinaryRow_ordinal_partial_cover: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.semanticBinaryRow_ordinal_partial_cover` of [lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticOrdinalRowOrbitCovers.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticOrdinalRowOrbitCovers.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open scoped ZFSet`, `open SetRealization SetFormula`):
--
--   ```lean
--   theorem semanticBinaryRow_ordinal_partial_cover
--       (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
--       (mu : ZFSet.{u}) (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu)
--       (small : M.groundEmbeddable s.nonbottom.carrier mu) :
--       letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
--       letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨s.carrier, hL⟩
--       let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
--       let c := SetMembers.presentation (M.smallPartialFunctions
--         (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
--       ∀ (T T2 : ZFSet.{u}) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
--         (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
--         (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
--         (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (act.act c.pairEmpty g tau).val ∈ T)
--         (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (act.act c.pairEmpty g tau).val ∈ T2)
--         (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
--           HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
--         (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
--           HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
--         (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
--         (ordinal : ordinalSetProperty stages)
--         (trace : OrdinalRecursionTrace (fun level prior stage => stage =
--           M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
--             b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
--             (supportBasisCode s b a.principalFix) T T2 level prior) stages history),
--       let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
--       let two := M.natSetCode_mem separation infinite 2
--       let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
--       let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
--       let forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
--       let omega := M.omega_mem separation infinite
--       let topMem := c.encode_mem ⊤
--       let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
--         fun r hr => by
--           obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
--           exact (c.pair_mem_conditionOrder r ⊤).2 le_top
--       let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
--         (supportBasisCode s b a.principalFix) T T2 stages history
--       let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
--         (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
--         (supportBasisCode s b a.principalFix) T T2 ordinal trace
--       letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
--       letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
--         run.carriers ordinal carrier (c.encode ⊤) topMem topRows
--       let upper := SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages packed)
--       let upperAct := M.semanticStructuralAction c act b s a ⊥ directed T T2 (c.encode ⊤)
--         pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
--         nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace
--       let inclusion := M.refinementHistoryRowEmbedding c T stages packed run ordinal carrier
--       let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
--       let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
--       let RowTerms := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
--       ∃ validRows : ∀ z ∈ RowTerms, IsName c z,
--       ∃ validUpper : ∀ z ∈ Name.renamedFamily upper inclusion RowTerms validRows, IsName upper z,
--       let rowName := Name.familySet (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed))
--         (Name.renamedFamily upper inclusion RowTerms validRows) validUpper
--       ∀ (H : ConditionFilter (SetMembers (M.refinementHistoryForcing c.carrier T stages packed))),
--         H.GenericFor (formulaFamily (M.nameDomain upper)) →
--         let N := M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H
--         let Trow := Name.eval {p | H.mem p} rowName
--         Trow ∈ N.sets ∧
--         ∀ X ∈ N.sets, ∃ delta ∈ N.sets, ordinalSetProperty delta ∧
--           ∃ h ∈ N.sets, FunctionGraphOn delta h ∧
--             (∀ i hi, ZFSet.pair i hi ∈ h → PartialFunctionCode Trow (⋃₀ ⋃₀ hi) hi) ∧
--             ∀ x ∈ X, ∃ i ∈ delta, ∃ hi, ZFSet.pair i hi ∈ h ∧
--               ∃ u ∈ Trow, ZFSet.pair u x ∈ hi
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.FunctionGraphOn`, `OAI.PartitionPilot.Forcing.PartialFunctionCode`, `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.Forcing.natSetCode`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.natSetCode_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.omega_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.prod_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallFunctionOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallFunctionTop`, `OAI.PartitionPilot.Forcing.TransitiveGround.smallPartialFunctions`, `OAI.PartitionPilot.SetRealization.Presentation.encode_mem` and `OAI.PartitionPilot.SetRealization.SetMembers.presentation` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.ConditionFilter` and `OAI.PartitionPilot.Forcing.ConditionFilter.GenericFor` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix`, `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` and `OAI.PartitionPilot.SetRealization.Presentation.pair_mem_conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace`, `OAI.PartitionPilot.Forcing.Name.eval`, `OAI.PartitionPilot.Forcing.Name.familySet`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.PosetAction.conditionMapFamily`, `OAI.PartitionPilot.Forcing.SetFormula.formulaFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.nameDomain`, `OAI.PartitionPilot.Forcing.TransitiveGround.nonbottom_carrier_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.rowPositionSequences`, `OAI.PartitionPilot.Forcing.TransitiveGround.symmetricExtension`, `OAI.PartitionPilot.SetRealization.Presentation.nonbottom` and `OAI.PartitionPilot.SetRealization.Presentation.pairEmpty` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.rowTupleTerms`, `OAI.PartitionPilot.Forcing.Name.renamedFamily`, `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowNameGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.countableFunctionOrder_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.countablePartialFunctions_mem`, `OAI.PartitionPilot.Forcing.TransitiveGround.internalRowAction`, `OAI.PartitionPilot.Forcing.TransitiveGround.internalRowActionGraph_mem` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder_code` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryOrderTop` and `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryPartialOrder` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryRowEmbedding`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStage`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingTrace_recursiveOrder` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAction` (definitions bundle `OAIQ253P011` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet`, `OAI.PartitionPilot.Forcing.SetFormula.union` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundEmbeddable` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticOrdinalRowOrbitCovers.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.semanticBinaryRow_ordinal_partial_cover)

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
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
include order nodeMaps supports choice

theorem semanticBinaryRow_ordinal_partial_cover
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (mu : ZFSet.{u}) (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu)
    (small : M.groundEmbeddable s.nonbottom.carrier mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    ∀ (T T2 : ZFSet.{u}) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (act.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (act.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
          b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) T T2 level prior) stages history),
    let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
    let two := M.natSetCode_mem separation infinite 2
    let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    let forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
    let omega := M.omega_mem separation infinite
    let topMem := c.encode_mem ⊤
    let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) T T2 stages history
    let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
      (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) T T2 ordinal trace
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      run.carriers ordinal carrier (c.encode ⊤) topMem topRows
    let upper := SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages packed)
    let upperAct := M.semanticStructuralAction c act b s a ⊥ directed T T2 (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace
    let inclusion := M.refinementHistoryRowEmbedding c T stages packed run ordinal carrier
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let RowTerms := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∃ validRows : ∀ z ∈ RowTerms, IsName c z,
    ∃ validUpper : ∀ z ∈ Name.renamedFamily upper inclusion RowTerms validRows, IsName upper z,
    let rowName := Name.familySet (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed))
      (Name.renamedFamily upper inclusion RowTerms validRows) validUpper
    ∀ (H : ConditionFilter (SetMembers (M.refinementHistoryForcing c.carrier T stages packed))),
      H.GenericFor (formulaFamily (M.nameDomain upper)) →
      let N := M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H
      let Trow := Name.eval {p | H.mem p} rowName
      Trow ∈ N.sets ∧
      ∀ X ∈ N.sets, ∃ delta ∈ N.sets, ordinalSetProperty delta ∧
        ∃ h ∈ N.sets, FunctionGraphOn delta h ∧
          (∀ i hi, ZFSet.pair i hi ∈ h → PartialFunctionCode Trow (⋃₀ ⋃₀ hi) hi) ∧
          ∀ x ∈ X, ∃ i ∈ delta, ∃ hi, ZFSet.pair i hi ∈ h ∧
            ∃ u ∈ Trow, ZFSet.pair u x ∈ hi := by
  sorry

end PartitionPilot.Forcing.TransitiveGround

end OAI
end
