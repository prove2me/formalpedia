-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_exists_initialRecursionSeed
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.exists_initialRecursionSeed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:12:39.659991+00:00
-- url     : https://prove2.me/theorems/308e2da8-2579-464c-b5a2-51e2336fcb3f
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.exists_initialRecursionSeed: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.exists_initialRecursionSeed` of [lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundMainPrefixSelectedStepTotality.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundMainPrefixSelectedStepTotality.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open SetFormula SetRealization`):
--
--   ```lean
--   theorem exists_initialRecursionSeed
--       (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
--       (unions : Realize M.sets SetFormula.union Fin.elim0)
--       (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
--       (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
--       (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
--       let C := M.groundOmegaOne pairing unions powers separation collection infinite
--       ∃ level : GroundMainCandidateLevel M K,
--         ∃ seed : GroundInitialMainSeedData M K C,
--           ∃ run : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
--               (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2),
--             ∃ initial : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
--                 (rationalLtGraph seed.fractionCode) pairing unions powers separation
--                 {i : Fin 2 // run.key i ∈ natSetCode 1},
--               level.recursionPrefixes C C C (rationalCarrier seed.fractionCode)
--                 (rationalLtGraph seed.fractionCode) ∈ M.sets ∧
--               initial.code ∈ level.recursionPrefixes C C C (rationalCarrier seed.fractionCode)
--                 (rationalLtGraph seed.fractionCode) ∧
--               initial.indices = natSetCode 1 ∧ initial.PreservesOldProfiles ∧
--               initial.code ∈ M.sets ∧ ZFSet.rank initial.code < ZFSet.rank K ∧
--               initial.stageGraph = graphRestriction (natSetCode 1) run.stageGraph ∧
--               initial.transitionGraph = graphRestriction (chronologyPairs (natSetCode 1)) run.transitionGraph ∧
--               ∃ i, initial.key i = natSetCode 0 ∧ initial.diagram.stage i = seed.source
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.natSetCode` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.chronologyPairs` and `OAI.PartitionPilot.Forcing.graphRestriction` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.rationalCarrier` and `OAI.PartitionPilot.Forcing.rationalLtGraph` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.GroundChronologicalMainStage` and `OAI.PartitionPilot.Forcing.GroundChronologicalMainDiagram` (definitions bundle `OAIQ253P004` of this split); `OAI.PartitionPilot.Forcing.GroundInitialMainSeedData`, `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel`, `OAI.PartitionPilot.Forcing.GroundMainPrefix`, `OAI.PartitionPilot.Forcing.GroundMainCandidateLevel.recursionPrefixes`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.PreservesOldProfiles`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.code`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.indices`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.stageGraph` and `OAI.PartitionPilot.Forcing.GroundMainPrefix.transitionGraph` (definitions bundle `OAIQ253P006` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.groundOmegaOne` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.GroundStandardInaccessible`, `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet` and `OAI.PartitionPilot.Forcing.SetFormula.union` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundMainFinalFulfillment` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Transfinite/GroundMainPrefixSelectedStepTotality.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.exists_initialRecursionSeed)

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

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_initialRecursionSeed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K,
      ∃ seed : GroundInitialMainSeedData M K C,
        ∃ run : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
            (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2),
          ∃ initial : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) pairing unions powers separation
              {i : Fin 2 // run.key i ∈ natSetCode 1},
            level.recursionPrefixes C C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∈ M.sets ∧
            initial.code ∈ level.recursionPrefixes C C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            initial.indices = natSetCode 1 ∧ initial.PreservesOldProfiles ∧
            initial.code ∈ M.sets ∧ ZFSet.rank initial.code < ZFSet.rank K ∧
            initial.stageGraph = graphRestriction (natSetCode 1) run.stageGraph ∧
            initial.transitionGraph = graphRestriction (chronologyPairs (natSetCode 1)) run.transitionGraph ∧
            ∃ i, initial.key i = natSetCode 0 ∧ initial.diagram.stage i = seed.source := by
  sorry

end TransitiveGround

open SetFormula SetRealization
universe u v w

end PartitionPilot.Forcing

end OAI
end
