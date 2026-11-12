-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_GroundInitialMainSuccessorData_exists_rankedTargetSerialization
-- name    : OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData.exists_rankedTargetSerialization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:05:11.650566+00:00
-- url     : https://prove2.me/theorems/2823373d-519f-4f99-975f-440a25454377
-- title:
--   OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData.exists_rankedTargetSerialization: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData.exists_rankedTargetSerialization` of [lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundOmegaOneTaskBearingSuccessorFunction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundOmegaOneTaskBearingSuccessorFunction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData`, with `open SetFormula`):
--
--   ```lean
--   theorem exists_rankedTargetSerialization
--       (prior : GroundSerializedChronology M (insert source.cutoff source.cutoff) C D rD)
--       (priorRank : ZFSet.rank prior.code < ZFSet.rank K)
--       (agreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
--         prior.fields.value j s = source.history.fieldValue j s) :
--       ∃ serial : GroundSerializedChronology M (insert certificate.target.cutoff certificate.target.cutoff) C D rD,
--         serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
--         serial.code ∈ level.validChronologies C D rD ∧
--         (∀ j s, s ∈ insert certificate.target.cutoff certificate.target.cutoff →
--           serial.fields.value j s = certificate.target.history.fieldValue j s) ∧
--         serial.fields.value 0 certificate.target.cutoff = certificate.target.stage.carrier ∧
--         serial.fields.value 1 certificate.target.cutoff = certificate.target.stage.order ∧
--         serial.fields.value 2 certificate.target.cutoff = certificate.target.stage.meetGraph ∧
--         serial.fields.value 3 certificate.target.cutoff = certificate.target.birth ∧
--         serial.fields.value 4 certificate.target.cutoff = certificate.target.stage.height
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.GroundMainStage` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.GroundChronologicalMainStage`, `OAI.PartitionPilot.Forcing.GroundInaccessibleConditions`, `OAI.PartitionPilot.Forcing.GroundSerializedChronology`, `OAI.PartitionPilot.Forcing.GroundChronologicalHistory.fieldValue`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainStage.Invariant`, `OAI.PartitionPilot.Forcing.GroundChronologicalMainStage.birth`, `OAI.PartitionPilot.Forcing.GroundChronologyFields.value` and `OAI.PartitionPilot.Forcing.GroundSerializedChronology.code` (definitions bundle `OAIQ253P004` of this split); `OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData`, `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel` and `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.validChronologies` (definitions bundle `OAIQ253P006` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet` and `OAI.PartitionPilot.Forcing.SetFormula.union` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proofs of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_initialRecursionSeed` and `OAI.PartitionPilot.Forcing.TransitiveGround.omegaOne_taskBearingSuccessor_total` of this split import it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundOmegaOneTaskBearingSuccessorFunction.lean (declaration OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData.exists_rankedTargetSerialization)

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
import Definitions.Def_OAIQ253P006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (invariant : source.Invariant K Labels) (level : GroundMainCandidateLevel M K)
local notation "births" => certificate.births
include pairing unions powers separation collection infinite choice hK conditions invariant

theorem exists_rankedTargetSerialization
    (prior : GroundSerializedChronology M (insert source.cutoff source.cutoff) C D rD)
    (priorRank : ZFSet.rank prior.code < ZFSet.rank K)
    (agreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
      prior.fields.value j s = source.history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert certificate.target.cutoff certificate.target.cutoff) C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
      serial.code ∈ level.validChronologies C D rD ∧
      (∀ j s, s ∈ insert certificate.target.cutoff certificate.target.cutoff →
        serial.fields.value j s = certificate.target.history.fieldValue j s) ∧
      serial.fields.value 0 certificate.target.cutoff = certificate.target.stage.carrier ∧
      serial.fields.value 1 certificate.target.cutoff = certificate.target.stage.order ∧
      serial.fields.value 2 certificate.target.cutoff = certificate.target.stage.meetGraph ∧
      serial.fields.value 3 certificate.target.cutoff = certificate.target.birth ∧
      serial.fields.value 4 certificate.target.cutoff = certificate.target.stage.height := by
  sorry

end PartitionPilot.Forcing.GroundInitialMainSuccessorData

end OAI
end
