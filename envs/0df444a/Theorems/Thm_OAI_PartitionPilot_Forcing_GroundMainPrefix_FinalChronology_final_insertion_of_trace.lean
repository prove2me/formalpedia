-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalChronology_final_insertion_of_trace
-- name    : OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalChronology.final_insertion_of_trace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:12:32.515347+00:00
-- url     : https://prove2.me/theorems/907a5529-6100-48b9-9590-76db720a1a69
-- title:
--   OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalChronology.final_insertion_of_trace: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalChronology.final_insertion_of_trace` of [lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundMainPrefixFinalInsertion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundMainPrefixFinalInsertion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalChronology`, with `open SetFormula`):
--
--   ```lean
--   theorem final_insertion_of_trace (i₀ : I)
--       (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
--       (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       {B seed f g p : ZFSet.{u}}
--       (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
--         (M.groundOmegaOne pairing unions powers separation collection infinite) p)
--       (chosen : ∀ old next, ZFSet.pair old next ∈ g →
--         MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
--       (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
--         TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
--       (indices : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
--       (extension : MainPrefixHistoryExtends p run.code) (preserved : run.PreservesOldProfiles)
--       (hLabels : Labels ∈ M.sets) (coordinateSmall : M.groundEmbeddable D ZFSet.omega)
--       (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
--       {c e d F : ZFSet.{u}} (hc : c ∈ run.limitPoints) (he : e ∈ run.limitPoints)
--       (hd : d ∈ run.limitPoints) (hF : F ∈ M.sets)
--       (filter : MeetFilterCode run.limitPoints run.limitOrder run.limitMeetGraph F)
--       (lower : ZFSet.pair c e ∈ run.limitOrder) (strict : ZFSet.pair e c ∉ run.limitOrder)
--       (bound : ZFSet.pair c d ∈ run.limitOrder)
--       (above : ∀ x ∈ F, ZFSet.pair e x ∈ run.limitOrder) :
--       ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
--         FinalInsertionFamiliesCode Labels run.limitPoints run.limitActors run.limitOrder
--           run.limitMeetGraph run.limitAction c e d F caps actors
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.MeetFilterCode` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.FinalInsertionFamiliesCode` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.MainPrefixHistoryExtends`, `OAI.PartitionPilot.Forcing.MainPrefixTraceStepCode` and `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel`, `OAI.PartitionPilot.Forcing.GroundMainPrefix`, `OAI.PartitionPilot.Forcing.MainPrefixConditionalStepCode`, `OAI.PartitionPilot.Forcing.TaskBearingMainSuccessorCode`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalChronology`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.PreservesOldProfiles`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.code`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.indices`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.limitAction`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.limitActors`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.limitMeetGraph`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.limitOrder` and `OAI.PartitionPilot.Forcing.GroundMainPrefix.limitPoints` (definitions bundle `OAIQ253P006` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.groundOmegaOne` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet`, `OAI.PartitionPilot.Forcing.SetFormula.union` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundEmbeddable` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundMainPrefixFinalInsertion.lean (declaration OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalChronology.final_insertion_of_trace)

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

namespace PartitionPilot.Forcing

namespace GroundMainPrefix.FinalChronology
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)
include chronology

theorem final_insertion_of_trace (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
      (M.groundOmegaOne pairing unions powers separation collection infinite) p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (indices : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (extension : MainPrefixHistoryExtends p run.code) (preserved : run.PreservesOldProfiles)
    (hLabels : Labels ∈ M.sets) (coordinateSmall : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {c e d F : ZFSet.{u}} (hc : c ∈ run.limitPoints) (he : e ∈ run.limitPoints)
    (hd : d ∈ run.limitPoints) (hF : F ∈ M.sets)
    (filter : MeetFilterCode run.limitPoints run.limitOrder run.limitMeetGraph F)
    (lower : ZFSet.pair c e ∈ run.limitOrder) (strict : ZFSet.pair e c ∉ run.limitOrder)
    (bound : ZFSet.pair c d ∈ run.limitOrder)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ run.limitOrder) :
    ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
      FinalInsertionFamiliesCode Labels run.limitPoints run.limitActors run.limitOrder
        run.limitMeetGraph run.limitAction c e d F caps actors := by
  sorry

end GroundMainPrefix.FinalChronology

end PartitionPilot.Forcing

end OAI
end
