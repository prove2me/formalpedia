-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_structuralAssignment_prepared_insertion_collision
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.structuralAssignment_prepared_insertion_collision
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:13:56.018229+00:00
-- url     : https://prove2.me/theorems/4634d9e7-a201-42b1-9c96-8f23981e2ced
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.structuralAssignment_prepared_insertion_collision: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.structuralAssignment_prepared_insertion_collision` of [lean/OAI/SetTheory/PartitionPrinciple/Geometry/GroundPreparedStructuralInsertionCollisions.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Geometry/GroundPreparedStructuralInsertionCollisions.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open SetFormula SetRealization`):
--
--   ```lean
--   theorem structuralAssignment_prepared_insertion_collision
--       (small : M.sets.Countable)
--       {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
--       (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
--         (a.actionGraph s t)) ∈ history)
--       (I S mu positions tuples sourceA : ZFSet.{u})
--       (positionSupport : ∀ (D : L), ∀ f ∈ S, ∀ u : Name s, ZFSet.pair f u.val ∈ tuples →
--         RowPositionBound mu positions b.conditionOrder f (b.encode D) →
--         d.principalFix D ≤ a.stabilizer s u)
--       (h : G) (D K V C E : L) (U Rf Rc u w newU newW : (M.nameDomain s).names)
--       (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
--         M.niceRefinementIndices a s b d level T T2 system.valid1)
--       (hu : u.val.val ∈ T) (hw : w.val.val ∈ T)
--       (hNewU : newU.val.val ∈ T) (hNewW : newW.val.val ∈ T)
--       (p q : P) (qp : q ≤ p) (qh : q ≤ a.iso h p)
--       (fixed : h ∈ d.principalFix V) (cap : d.iso h D ≤ K)
--       (avoid : E ≤ K → E ≤ V) (F B f e names : Fin 2 → ZFSet.{u})
--       (good : ∀ i, b.encode V ∉ F i → b.encode K ∉ F i) :
--       let fields := M.refinementLevelFormulaData a s b d level T T2 system.valid1
--       let image := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
--         (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA
--       let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT system.valid1
--       let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
--       stageOneAssignment idx u.val.val w.val.val ∈ sourceA →
--       ZFSet.pair (stageOneAssignment idx newU.val.val newW.val.val) (b.encode (d.iso h D)) ∈
--         stageOneDataBounds image I T S b.carrier mu positions b.conditionOrder
--           (refinementIndexFieldGraph I b.carrier 2) tuples →
--       stageOneRawTests M fields sourceA (s.encode p) → stageOneRawTests M fields image (s.encode q) →
--       (∀ i : Fin 2, PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
--         b.carrier b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder)
--         (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤)
--         ZFSet.omega ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain s).names) i).val.val
--         (F i) (B i) (f i) (e i) (names i)) →
--       E ≤ V ∧
--       stageOneRawCollision M fields idx u.val.val newU.val.val w.val.val newW.val.val (s.encode q) ∧
--       stageOneRawCollision M fields idx newU.val.val u.val.val newW.val.val w.val.val (s.encode q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.FunctionGraphOn`, `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.Forcing.canonicalMeetGraph`, `OAI.PartitionPilot.Forcing.stageOneAssignment`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundRelations` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.RowPositionBound` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.refinementIndexCode`, `OAI.PartitionPilot.Forcing.stageOneRawCollision`, `OAI.PartitionPilot.Forcing.stageOneRawTests`, `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.forcingStageCode`, `OAI.PartitionPilot.Forcing.refinementIndexFieldGraph`, `OAI.PartitionPilot.Forcing.stageOneDataBounds`, `OAI.PartitionPilot.Forcing.PosetAction.stabilizer`, `OAI.PartitionPilot.Forcing.TransitiveGround.nameDomain`, `OAI.PartitionPilot.Forcing.TransitiveGround.niceVisibilityGraph` and `OAI.PartitionPilot.Forcing.Name.NameDomain` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.niceRefinementIndices` and `OAI.PartitionPilot.Forcing.TransitiveGround.refinementLevelFormulaData` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.PreparedCertificateCode`, `OAI.PartitionPilot.Forcing.RefinementStageSystem` and `OAI.PartitionPilot.Forcing.TransitiveGround.stageOneClassName` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.structuralAssignmentImage` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet` and `OAI.PartitionPilot.Forcing.SetFormula.union` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_insertion_crossCollisions` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Geometry/GroundPreparedStructuralInsertionCollisions.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.structuralAssignment_prepared_insertion_collision)

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

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (level T T2 : ZFSet.{u})
variable (system : RefinementStageSystem M a s t b d base directed level T T2)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
include system pairing unions powers separation collection carrier order group nodes supports hLevel hT

theorem structuralAssignment_prepared_insertion_collision
    (small : M.sets.Countable)
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (I S mu positions tuples sourceA : ZFSet.{u})
    (positionSupport : ∀ (D : L), ∀ f ∈ S, ∀ u : Name s, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s u)
    (h : G) (D K V C E : L) (U Rf Rc u w newU newW : (M.nameDomain s).names)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hu : u.val.val ∈ T) (hw : w.val.val ∈ T)
    (hNewU : newU.val.val ∈ T) (hNewW : newW.val.val ∈ T)
    (p q : P) (qp : q ≤ p) (qh : q ≤ a.iso h p)
    (fixed : h ∈ d.principalFix V) (cap : d.iso h D ≤ K)
    (avoid : E ≤ K → E ≤ V) (F B f e names : Fin 2 → ZFSet.{u})
    (good : ∀ i, b.encode V ∉ F i → b.encode K ∉ F i) :
    let fields := M.refinementLevelFormulaData a s b d level T T2 system.valid1
    let image := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT system.valid1
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    stageOneAssignment idx u.val.val w.val.val ∈ sourceA →
    ZFSet.pair (stageOneAssignment idx newU.val.val newW.val.val) (b.encode (d.iso h D)) ∈
      stageOneDataBounds image I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples →
    stageOneRawTests M fields sourceA (s.encode p) → stageOneRawTests M fields image (s.encode q) →
    (∀ i : Fin 2, PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder)
      (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤)
      ZFSet.omega ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain s).names) i).val.val
      (F i) (B i) (f i) (e i) (names i)) →
    E ≤ V ∧
    stageOneRawCollision M fields idx u.val.val newU.val.val w.val.val newW.val.val (s.encode q) ∧
    stageOneRawCollision M fields idx newU.val.val u.val.val newW.val.val w.val.val (s.encode q) := by
  sorry

end PartitionPilot.Forcing.TransitiveGround

end OAI
end
