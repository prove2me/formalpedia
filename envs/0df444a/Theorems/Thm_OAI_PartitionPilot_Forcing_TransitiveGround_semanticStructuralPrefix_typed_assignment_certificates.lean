-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_typed_assignment_certificates
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_typed_assignment_certificates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:32:52.539095+00:00
-- url     : https://prove2.me/theorems/672f4ac3-efbb-4cea-aedf-81dc6ac5dde1
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_typed_assignment_certificates: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_typed_assignment_certificates` of [lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticAlignedCopyCollisions.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticAlignedCopyCollisions.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open scoped ZFSet`, `open SetRealization SetFormula`):
--
--   ```lean
--   theorem semanticStructuralPrefix_typed_assignment_certificates
--       (infinite : Realize M.sets infinity Fin.elim0)
--       (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       {row A : ZFSet.{u}}
--       (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair row A)) :
--       letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
--       letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
--         ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
--       let lower := SetMembers.presentation Q
--       let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
--         cutOrdinal carrier T valid1
--       let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
--       let upperQ := M.refinementHistoryForcing c.carrier T stages packed
--       ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
--         refinementIndexCode alpha (b.encode C) (b.encode E)
--           U.val.val Rf.val.val Rc.val.val ∈ fields 0 →
--         ∀ (u w : Name lower), u.val ∈ T → w.val ∈ T →
--         stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
--           U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
--         ∃ sourceRow sourceA, sourceA ∈ M.sets ∧ ZFSet.pair sourceRow sourceA ∈ upperQ ∧
--           sourceA ⊆ A ∧
--         ∃ k ∈ M.sets, ∃ enumerations ∈ M.sets, ∃ q : SetMembers Q,
--           ZFSet.pair (ZFSet.pair row A) (lower.encode q) ∈ rowAssignmentCutGraph upperQ (fields 7)
--             (refinementDataHistoryLevels stages packed T) alpha ∧
--           PreparedCertificateFamilyCode M (fields 7) (fields 8) (lower.encode q) (fields 10) (fields 11)
--             (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
--             ZFSet.omega (M.storedPreparationRequests sourceA fields)
--             (M.supportedEqualityCertificateBound b.carrier (M.groundRelations T upperQ))
--             (M.synchronizedEnumerationBound b.carrier (M.groundRelations T upperQ)) k enumerations ∧
--         ∀ side : Fin 2,
--           let request := Name.refinementClass T valid
--             (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
--             (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)
--           request.val ∈ M.storedPreparationRequests sourceA fields ∧ request.val ∈ M.sets ∧
--           IsName lower request.val ∧
--           HereditarilySymmetric act lower (d.principalSupportFamily base directed) request ∧
--           (∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} request ⊆
--             Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) ∧
--           ∃ F B f e names, F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
--             e ∈ M.sets ∧ names ∈ M.sets ∧
--             ZFSet.pair request.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
--             ZFSet.pair request.val (ZFSet.pair e names) ∈ enumerations ∧
--             PreparedCertificateCode M (fields 7) (fields 8) (lower.encode q) (fields 10) (fields 11)
--               (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
--               ZFSet.omega request.val F B f e names ∧
--             M.TypedPreparedCertificate act lower b T d.principalFix (fields 11)
--               (canonicalMeetGraph (fields 10) (fields 11)) ZFSet.omega request q F B f e names
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.Forcing.canonicalMeetGraph`, `OAI.PartitionPilot.Forcing.stageOneAssignment`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.groundRelations` and `OAI.PartitionPilot.SetRealization.SetMembers.presentation` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.ConditionFilter`, `OAI.PartitionPilot.Forcing.graphRestriction`, `OAI.PartitionPilot.Forcing.ordinalSetProperty_member` and `OAI.PartitionPilot.Forcing.rowAssignmentCutGraph` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.refinementIndexCode`, `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace`, `OAI.PartitionPilot.Forcing.Name.eval`, `OAI.PartitionPilot.Forcing.Name.familySet`, `OAI.PartitionPilot.Forcing.Name.refinementClass`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.PosetAction.conditionMapFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.nameDomain`, `OAI.PartitionPilot.SetRealization.Presentation.pairEmpty` and `OAI.PartitionPilot.Forcing.Name.NameDomain` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.refinementDataHistoryLevels`, `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementLevelFormulaData` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder_code` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.PreparedCertificateCode`, `OAI.PartitionPilot.Forcing.PreparedCertificateFamilyCode`, `OAI.PartitionPilot.Forcing.StoredPreparedConditionCode`, `OAI.PartitionPilot.Forcing.RecursiveRefinementDataHistory.restrict`, `OAI.PartitionPilot.Forcing.RecursiveRefinementOrderHistory`, `OAI.PartitionPilot.Forcing.TransitiveGround.TypedPreparedCertificate`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryOrderTop`, `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryPartialOrder`, `OAI.PartitionPilot.Forcing.TransitiveGround.storedPreparationRequests`, `OAI.PartitionPilot.Forcing.TransitiveGround.supportedEqualityCertificateBound` and `OAI.PartitionPilot.Forcing.TransitiveGround.synchronizedEnumerationBound` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryRowNameFamily_valid`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStage`, `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingTrace_recursiveOrder` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixAction` (definitions bundle `OAIQ253P011` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.setTransitive`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet` and `OAI.PartitionPilot.Forcing.SetFormula.union` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proofs of `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_aligned_copy_crossCollisions` and `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut` of this split import it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticAlignedCopyCollisions.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_typed_assignment_certificates)

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

theorem semanticStructuralPrefix_typed_assignment_certificates
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair row A)) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    let upperQ := M.refinementHistoryForcing c.carrier T stages packed
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val ∈ fields 0 →
      ∀ (u w : Name lower), u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
      ∃ sourceRow sourceA, sourceA ∈ M.sets ∧ ZFSet.pair sourceRow sourceA ∈ upperQ ∧
        sourceA ⊆ A ∧
      ∃ k ∈ M.sets, ∃ enumerations ∈ M.sets, ∃ q : SetMembers Q,
        ZFSet.pair (ZFSet.pair row A) (lower.encode q) ∈ rowAssignmentCutGraph upperQ (fields 7)
          (refinementDataHistoryLevels stages packed T) alpha ∧
        PreparedCertificateFamilyCode M (fields 7) (fields 8) (lower.encode q) (fields 10) (fields 11)
          (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
          ZFSet.omega (M.storedPreparationRequests sourceA fields)
          (M.supportedEqualityCertificateBound b.carrier (M.groundRelations T upperQ))
          (M.synchronizedEnumerationBound b.carrier (M.groundRelations T upperQ)) k enumerations ∧
      ∀ side : Fin 2,
        let request := Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)
        request.val ∈ M.storedPreparationRequests sourceA fields ∧ request.val ∈ M.sets ∧
        IsName lower request.val ∧
        HereditarilySymmetric act lower (d.principalSupportFamily base directed) request ∧
        (∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} request ⊆
          Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) ∧
        ∃ F B f e names, F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
          e ∈ M.sets ∧ names ∈ M.sets ∧
          ZFSet.pair request.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
          ZFSet.pair request.val (ZFSet.pair e names) ∈ enumerations ∧
          PreparedCertificateCode M (fields 7) (fields 8) (lower.encode q) (fields 10) (fields 11)
            (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
            ZFSet.omega request.val F B f e names ∧
          M.TypedPreparedCertificate act lower b T d.principalFix (fields 11)
            (canonicalMeetGraph (fields 10) (fields 11)) ZFSet.omega request q F B f e names := by
  sorry

end PartitionPilot.Forcing.TransitiveGround

end OAI
end
