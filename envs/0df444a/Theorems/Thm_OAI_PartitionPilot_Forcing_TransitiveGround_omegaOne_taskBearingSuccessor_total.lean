-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_omegaOne_taskBearingSuccessor_total
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.omegaOne_taskBearingSuccessor_total
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:22:48.694315+00:00
-- url     : https://prove2.me/theorems/37e148cb-9cc8-487d-a5d7-d36637b1e95c
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.omegaOne_taskBearingSuccessor_total: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.omegaOne_taskBearingSuccessor_total` of [lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundOmegaOneTaskBearingSuccessorFunction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundOmegaOneTaskBearingSuccessorFunction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open SetFormula`):
--
--   ```lean
--   theorem omegaOne_taskBearingSuccessor_total {K D rD c : ZFSet.{u}}
--       (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) (hc : c ∈ M.sets)
--       (dense : DenseOrderCode D rD) (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
--       (coordinateInjection : InjectionCode D ZFSet.omega c) (level : GroundMainCandidateLevel M K)
--       {s : ZFSet.{u}} (hs : s ∈ M.linkedMainStageCandidates level.carrier K C C D rD) :
--       ∃ t ∈ M.linkedMainStageCandidates level.carrier K C C D rD, ∃ z ∈ level.carrier,
--         TaskBearingMainSuccessorCode M K C C D rD ZFSet.omega s t z
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.DenseOrderCode` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel`, `OAI.PartitionPilot.Forcing.TaskBearingMainSuccessorCode` and `OAI.PartitionPilot.Forcing.TransitiveGround.linkedMainStageCandidates` (definitions bundle `OAIQ253P006` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.groundOmegaOne` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.GroundStandardInaccessible`, `OAI.PartitionPilot.Forcing.InjectionCode`, `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet` and `OAI.PartitionPilot.Forcing.SetFormula.union` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundMainFinalFulfillment` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundOmegaOneTaskBearingSuccessorFunction.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.omegaOne_taskBearingSuccessor_total)

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
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "C" => M.groundOmegaOne pairing unions powers separation collection infinite

include choice in
theorem omegaOne_taskBearingSuccessor_total {K D rD c : ZFSet.{u}}
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) (hc : c ∈ M.sets)
    (dense : DenseOrderCode D rD) (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c) (level : GroundMainCandidateLevel M K)
    {s : ZFSet.{u}} (hs : s ∈ M.linkedMainStageCandidates level.carrier K C C D rD) :
    ∃ t ∈ M.linkedMainStageCandidates level.carrier K C C D rD, ∃ z ∈ level.carrier,
      TaskBearingMainSuccessorCode M K C C D rD ZFSet.omega s t z := by
  sorry

end PartitionPilot.Forcing.TransitiveGround

end OAI
end
