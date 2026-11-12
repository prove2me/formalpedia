-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_exists_groundInitialMainSuccessor
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialMainSuccessor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:09:54.5672+00:00
-- url     : https://prove2.me/theorems/e834c806-c4d8-49e4-9ea2-5f6f56cacc5b
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialMainSuccessor: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialMainSuccessor` of [lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundMainSuccessorProfilePreservation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundMainSuccessorProfilePreservation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open SetFormula`):
--
--   ```lean
--   theorem exists_groundInitialMainSuccessor {D rD Labels c : ZFSet.{u}}
--       (source : GroundChronologicalMainStage M
--         (M.groundOmegaOne pairing unions powers separation collection infinite) D rD)
--       (hLabels : Labels ∈ M.sets) (hc : c ∈ M.sets)
--       (dense : DenseOrderCode D rD)
--       (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
--       (coordinateInjection : InjectionCode D ZFSet.omega c) :
--       Nonempty (GroundInitialMainSuccessorData M
--         (M.groundOmegaOne pairing unions powers separation collection infinite) D rD source Labels)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.DenseOrderCode` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.GroundChronologicalMainStage` (definitions bundle `OAIQ253P004` of this split); `OAI.PartitionPilot.Forcing.GroundInitialMainSuccessorData` (definitions bundle `OAIQ253P006` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.groundOmegaOne` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.InjectionCode`, `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet` and `OAI.PartitionPilot.Forcing.SetFormula.union` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proofs of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_initialRecursionSeed` and `OAI.PartitionPilot.Forcing.TransitiveGround.omegaOne_taskBearingSuccessor_total` of this split import it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundMainSuccessorProfilePreservation.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialMainSuccessor)

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P009

section

attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)

include choice in
theorem exists_groundInitialMainSuccessor {D rD Labels c : ZFSet.{u}}
    (source : GroundChronologicalMainStage M
      (M.groundOmegaOne pairing unions powers separation collection infinite) D rD)
    (hLabels : Labels ∈ M.sets) (hc : c ∈ M.sets)
    (dense : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c) :
    Nonempty (GroundInitialMainSuccessorData M
      (M.groundOmegaOne pairing unions powers separation collection infinite) D rD source Labels) := by
  sorry

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end
