-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainCandidateLevel_exists_groundConditionalPrefixFunction
-- name    : OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.exists_groundConditionalPrefixFunction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:15:51.767096+00:00
-- url     : https://prove2.me/theorems/bf845182-7ee8-407c-a152-d85b29c3f717
-- title:
--   OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.exists_groundConditionalPrefixFunction: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.exists_groundConditionalPrefixFunction` of [lean/OAI/SetTheory/PartitionPrinciple/Forcing/GroundMainConditionalTotality.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Forcing/GroundMainConditionalTotality.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel`, with `open SetFormula SetRealization`):
--
--   ```lean
--   theorem exists_groundConditionalPrefixFunction
--       (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
--       (unions : Realize M.sets SetFormula.union Fin.elim0)
--       (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
--       (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
--       (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       {Labels C D rD f : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
--       (hLabels : Labels ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
--       (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
--       (hf : f ∈ M.sets)
--       (function : ZFSet.IsFunc (M.linkedMainStageCandidates level.carrier K Labels C D rD)
--         (ZFSet.prod level.carrier level.carrier) f)
--       (selected : f ⊆ M.taskBearingSuccessorRelation
--         (M.linkedMainStageCandidates level.carrier K Labels C D rD) level.carrier K Labels C D rD) :
--       let S := level.recursionPrefixes
--         (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD
--       ∃ g ∈ M.sets, ZFSet.IsFunc S S g ∧
--         g ⊆ M.mainPrefixConditionalRelation S K Labels C D rD ZFSet.omega f ∧
--         ∀ old next, ZFSet.pair old next ∈ g →
--           next ∈ S ∧ MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel`, `OAI.PartitionPilot.Forcing.MainPrefixConditionalStepCode`, `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.recursionPrefixes`, `OAI.PartitionPilot.Forcing.TransitiveGround.linkedMainStageCandidates`, `OAI.PartitionPilot.Forcing.TransitiveGround.mainPrefixConditionalRelation` and `OAI.PartitionPilot.Forcing.TransitiveGround.taskBearingSuccessorRelation` (definitions bundle `OAIQ253P006` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.groundOmegaOne` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.GroundStandardInaccessible`, `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet` and `OAI.PartitionPilot.Forcing.SetFormula.union` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundMainFinalFulfillment` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Forcing/GroundMainConditionalTotality.lean (declaration OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.exists_groundConditionalPrefixFunction)

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

section

namespace PartitionPilot.Forcing.GroundMainCandidateLevel
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

theorem exists_groundConditionalPrefixFunction
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Labels C D rD f : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (hLabels : Labels ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (hf : f ∈ M.sets)
    (function : ZFSet.IsFunc (M.linkedMainStageCandidates level.carrier K Labels C D rD)
      (ZFSet.prod level.carrier level.carrier) f)
    (selected : f ⊆ M.taskBearingSuccessorRelation
      (M.linkedMainStageCandidates level.carrier K Labels C D rD) level.carrier K Labels C D rD) :
    let S := level.recursionPrefixes
      (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD
    ∃ g ∈ M.sets, ZFSet.IsFunc S S g ∧
      g ⊆ M.mainPrefixConditionalRelation S K Labels C D rD ZFSet.omega f ∧
      ∀ old next, ZFSet.pair old next ∈ g →
        next ∈ S ∧ MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next := by
  sorry

end PartitionPilot.Forcing.GroundMainCandidateLevel

end

end OAI
end
